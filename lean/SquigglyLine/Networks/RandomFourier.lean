/-
Random Fourier features: the Fourier lift, averaged, is the Gaussian bump.

`FourierLift.lean` shows that the kernel of the Fourier lift of frequency
`frequency` is `cos (frequency * (input - other_input))`. `RadialBasis.lean`
uses the Gaussian bump. This file joins the two: draw the frequency from a
bell curve of variance `variance`, and the average of the Fourier kernel is
the bump `exp (-variance * gap² / 2)`.

So a wide layer of random cosine features and a radial basis network have
the same kernel, on average.

Theorems:
* `integral_cos_gaussian`            the average cosine under a bell curve is
                                     a bump;
* `integral_liftKernel_fourierLift`  the average Fourier kernel is the
                                     radial basis kernel.
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import SquigglyLine.Networks.FourierLift
import SquigglyLine.Networks.RadialBasis

namespace SquigglyLine

open MeasureTheory ProbabilityTheory NNReal

/-- **The average cosine under a bell curve is a bump.** For a frequency drawn
from the bell curve of mean zero and variance `variance`, the mean of
`cos (gap * frequency)` is `exp (-variance * gap² / 2)`. -/
theorem integral_cos_gaussian
    (variance : ℝ≥0)
    (gap : ℝ) :
    let bell_curve     := gaussianReal 0 variance
    let average_cosine := ∫ frequency, Real.cos (gap * frequency) ∂bell_curve
    let bump           := Real.exp (-(variance * gap ^ 2) / 2)  -- the Gaussian characteristic function at `gap`
    average_cosine = bump := by
  unfold_named_pieces
  have angle_as_real_cast : ∀ frequency : ℝ,
      (gap : ℂ) * frequency * Complex.I
        = ((gap * frequency : ℝ) : ℂ) * Complex.I := fun frequency => by
    push_cast
    ring
  -- The wave `exp (i * gap * frequency)` has size one, so it is integrable.
  have integrable_wave :
      Integrable
        (fun frequency : ℝ => Complex.exp (gap * frequency * Complex.I))
        (gaussianReal 0 variance) := by
    refine (integrable_const (1 : ℝ)).mono' ?_
      (ae_of_all _ fun frequency => ?_)
    · exact (by fun_prop : Continuous fun frequency : ℝ =>
        Complex.exp (gap * frequency * Complex.I)).aestronglyMeasurable
    · rw [angle_as_real_cast, Complex.norm_exp_ofReal_mul_I]
  have real_part_integral :
      ∫ frequency, RCLike.re (Complex.exp (gap * frequency * Complex.I))
          ∂(gaussianReal 0 variance)
        = RCLike.re (∫ frequency, Complex.exp (gap * frequency * Complex.I)
          ∂(gaussianReal 0 variance)) := integral_re integrable_wave
  have real_part_is_cos : ∀ frequency : ℝ,
      RCLike.re (Complex.exp (gap * frequency * Complex.I))
        = Real.cos (gap * frequency) :=
    fun frequency => by
      rw [angle_as_real_cast]
      exact Complex.exp_ofReal_mul_I_re _
  simp only [real_part_is_cos] at real_part_integral
  -- The characteristic function of the bell curve gives the integral of the
  -- wave.
  have characteristic_function :
      ∫ frequency, Complex.exp (gap * frequency * Complex.I)
          ∂(gaussianReal 0 variance)
        = Complex.exp
          (gap * ((0 : ℝ) : ℂ) * Complex.I - variance * gap ^ 2 / 2) := by
    rw [← charFun_apply_real, charFun_gaussianReal]
  have exponent_is_real :
      (gap : ℂ) * ((0 : ℝ) : ℂ) * Complex.I - variance * gap ^ 2 / 2
        = ((-(variance * gap ^ 2) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [real_part_integral, characteristic_function, exponent_is_real]
  exact Complex.exp_ofReal_re _

/-- **Random Fourier features give the radial basis kernel.** Average the
kernel of the Fourier lift over frequencies drawn from the bell curve of
variance `variance`. The result is the Gaussian bump of the gap between the
two inputs. -/
theorem integral_liftKernel_fourierLift
    (variance : ℝ≥0)
    (input other_input : ℝ) :
    let bell_curve     := gaussianReal 0 variance
    let average_kernel :=
      ∫ frequency,
        GET_LIFT_KERNEL (LIFT_BY_FOURIER frequency) input other_input
          ∂bell_curve
    let gap            := input - other_input
    let bump           := Real.exp (-(variance * gap ^ 2) / 2)  -- the radial basis kernel at distance `gap`
    average_kernel = bump := by
  unfold_named_pieces
  have kernel_is_cosine : ∀ frequency : ℝ,
      GET_LIFT_KERNEL (LIFT_BY_FOURIER frequency) input other_input
        = Real.cos ((input - other_input) * frequency) :=
    fun frequency => by
      have kernel_eq :
          GET_LIFT_KERNEL (LIFT_BY_FOURIER frequency) input other_input
            = Real.cos (frequency * (input - other_input)) :=
        liftKernel_fourierLift frequency input other_input
      rw [kernel_eq, mul_comm]
  simp only [kernel_is_cosine]
  exact integral_cos_gaussian variance (input - other_input)

end SquigglyLine
