/-
Random Fourier features: the Fourier lift, averaged, is the Gaussian bump.

`FourierLift.lean` shows that the kernel of the Fourier lift of frequency `w`
is `cos (w * (x - x'))`. `RadialBasis.lean` uses the Gaussian bump. This file
joins the two: draw the frequency from a bell curve of variance `v`, and the
average of the Fourier kernel is the bump `exp (-v * gap² / 2)`.

So a wide layer of random cosine features and a radial basis network have
the same kernel, on average.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Theorems: `integral_cos_gaussian`, `integral_liftKernel_fourierLift`.
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import SquigglyLine.Networks.FourierLift
import SquigglyLine.Networks.RadialBasis

namespace SquigglyLine

open MeasureTheory ProbabilityTheory NNReal

/-- **The average cosine under a bell curve is a bump.** For a frequency `w` drawn from the
bell curve of mean zero and variance `v`, the mean of `cos (t * w)` is `exp (-v * t² / 2)`. -/
theorem integral_cos_gaussian (v : ℝ≥0) (t : ℝ) :
    ∫ w, Real.cos (t * w) ∂(gaussianReal 0 v) = Real.exp (-(v * t ^ 2) / 2) := by
  have hrewrite : ∀ x : ℝ, (t : ℂ) * x * Complex.I = ((t * x : ℝ) : ℂ) * Complex.I := fun x => by
    push_cast
    ring
  have hint : Integrable (fun x : ℝ => Complex.exp (t * x * Complex.I)) (gaussianReal 0 v) := by
    refine (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all _ fun x => ?_)
    · exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (t * x * Complex.I)).aestronglyMeasurable
    · rw [hrewrite, Complex.norm_exp_ofReal_mul_I]
  have hre : ∫ x, RCLike.re (Complex.exp (t * x * Complex.I)) ∂(gaussianReal 0 v)
      = RCLike.re (∫ x, Complex.exp (t * x * Complex.I) ∂(gaussianReal 0 v)) := integral_re hint
  have hcos : ∀ x : ℝ, RCLike.re (Complex.exp (t * x * Complex.I)) = Real.cos (t * x) :=
    fun x => by
      rw [hrewrite]
      exact Complex.exp_ofReal_mul_I_re _
  simp only [hcos] at hre
  have hchar : ∫ x, Complex.exp (t * x * Complex.I) ∂(gaussianReal 0 v)
      = Complex.exp (t * ((0 : ℝ) : ℂ) * Complex.I - v * t ^ 2 / 2) := by
    rw [← charFun_apply_real, charFun_gaussianReal]
  have hreal : (t : ℂ) * ((0 : ℝ) : ℂ) * Complex.I - v * t ^ 2 / 2
      = ((-(v * t ^ 2) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hre, hchar, hreal]
  exact Complex.exp_ofReal_re _

/-- **Random Fourier features give the radial basis kernel.** Average the kernel of the
Fourier lift over frequencies drawn from the bell curve of variance `v`. The result is the
Gaussian bump of the gap between the two inputs. -/
theorem integral_liftKernel_fourierLift (v : ℝ≥0) (x x' : ℝ) :
    ∫ w, GET_LIFT_KERNEL (LIFT_BY_FOURIER w) x x' ∂(gaussianReal 0 v)
      = Real.exp (-(v * (x - x') ^ 2) / 2) := by
  have hkernel : ∀ w : ℝ, GET_LIFT_KERNEL (LIFT_BY_FOURIER w) x x' = Real.cos ((x - x') * w) :=
    fun w => by
      have h : GET_LIFT_KERNEL (LIFT_BY_FOURIER w) x x' = Real.cos (w * (x - x')) :=
        liftKernel_fourierLift w x x'
      rw [h, mul_comm]
  simp only [hkernel]
  exact integral_cos_gaussian v (x - x')

end SquigglyLine
