/-
The Fourier lift: winding the input round a circle.

The lift `x ↦ (cos (w x), sin (w x))` winds the line round the unit circle,
`w` times as fast as `x` moves. A flat plane over that circle is a sine wave
downstairs.

* `liftedModel_fourierLift` : weights `(a, b)` give `a cos (w x) + b sin (w x)`.
* `liftKernel_fourierLift` : the kernel of two inputs is `cos (w (x - x'))`.
  It depends only on how far apart they are.
* `norm_fourierLift_sub_sq` : two lifted points are `√(2 - 2 cos (w (x - x')))`
  apart.
* `lipschitzWith_fourierLift` : so the lift stretches distances by at most
  `|w|`.
* `lipschitzWith_liftedModel_fourierLift` : and the wave is no steeper than
  the size of its weights times the frequency.

Shift invariance, for any lift:
* `liftedModel_shift` : if the kernel depends only on how far apart two inputs
  are, shifting the data and the question together changes no answer.
* `liftKernel_fourierLift_shift` : the Fourier lift is such a lift.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import SquigglyLine.Networks.Lift

namespace SquigglyLine

open NNReal

/-! ### The lift -/

/-- Wind the input round the unit circle at frequency `w`. -/
noncomputable def LIFT_BY_FOURIER (w x : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[Real.cos (w * x), Real.sin (w * x)]

/-- **A flat plane over the circle is a wave.** -/
theorem liftedModel_fourierLift (w a b x : ℝ) :
    EVALUATE_LIFTED_MODEL (LIFT_BY_FOURIER w) !₂[a, b] x = a * Real.cos (w * x) + b * Real.sin (w * x) := by
  simp [EVALUATE_LIFTED_MODEL, LIFT_BY_FOURIER, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- **The kernel sees only the gap.** The overlap of two lifted inputs is the cosine of the
frequency times how far apart they are. -/
theorem liftKernel_fourierLift (w x x' : ℝ) :
    GET_LIFT_KERNEL (LIFT_BY_FOURIER w) x x' = Real.cos (w * (x - x')) := by
  simp [GET_LIFT_KERNEL, LIFT_BY_FOURIER, PiLp.inner_apply, Fin.sum_univ_two, mul_sub, Real.cos_sub,
    mul_comm]

theorem liftKernel_fourierLift_shift (w d x x' : ℝ) :
    GET_LIFT_KERNEL (LIFT_BY_FOURIER w) (x + d) (x' + d) = GET_LIFT_KERNEL (LIFT_BY_FOURIER w) x x' := by
  rw [liftKernel_fourierLift, liftKernel_fourierLift, add_sub_add_right_eq_sub]

/-! ### Its stretch -/

theorem norm_fourierLift_sub_sq (w x x' : ℝ) :
    ‖LIFT_BY_FOURIER w x - LIFT_BY_FOURIER w x'‖ ^ 2 = 2 - 2 * Real.cos (w * (x - x')) := by
  have hkernel (a b : ℝ) :
      inner ℝ (LIFT_BY_FOURIER w a) (LIFT_BY_FOURIER w b) = Real.cos (w * (a - b)) :=
    liftKernel_fourierLift w a b
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, hkernel,
    hkernel, hkernel, sub_self, sub_self, mul_zero, Real.cos_zero]
  ring

/-- **The Fourier lift stretches by at most its frequency.** -/
theorem lipschitzWith_fourierLift (w : ℝ) : LipschitzWith ‖w‖₊ (LIFT_BY_FOURIER w) := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  have hcos := Real.one_sub_sq_div_two_le_cos (x := w * (x - x'))
  have hsquare : ‖LIFT_BY_FOURIER w x - LIFT_BY_FOURIER w x'‖ ^ 2 ≤ (|w| * |x - x'|) ^ 2 := by
    rw [norm_fourierLift_sub_sq, ← abs_mul, sq_abs]
    linarith
  rw [dist_eq_norm, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hsquare

/-- **A wave is no steeper than its size times its frequency.** -/
theorem lipschitzWith_liftedModel_fourierLift (w : ℝ) (θ : EuclideanSpace ℝ (Fin 2)) :
    LipschitzWith (‖θ‖₊ * ‖w‖₊) (EVALUATE_LIFTED_MODEL (LIFT_BY_FOURIER w) θ) :=
  lipschitzWith_liftedModel (lipschitzWith_fourierLift w) θ

/-! ### Shift invariance -/

section Shift

variable {X Θ ι : Type*} [Add X] [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]

/-- **Shift the data and the question together and no answer changes.** This holds whenever
the kernel depends only on how far apart two inputs are. -/
theorem liftedModel_shift (φ : X → Θ)
    (hshift : ∀ d x x', GET_LIFT_KERNEL φ (x + d) (x' + d) = GET_LIFT_KERNEL φ x x') (s : Finset ι)
    (xs : ι → X) (c : ι → ℝ) (x d : X) :
    EVALUATE_LIFTED_MODEL φ (∑ i ∈ s, c i • φ (xs i + d)) (x + d)
      = EVALUATE_LIFTED_MODEL φ (∑ i ∈ s, c i • φ (xs i)) x := by
  have hmoved := liftedModel_add_sum φ s 0 (fun i => xs i + d) c (x + d)
  have hplain := liftedModel_add_sum φ s 0 xs c x
  rw [zero_add] at hmoved hplain
  rw [hmoved, hplain]
  simp only [hshift, EVALUATE_LIFTED_MODEL, inner_zero_left]

end Shift

end SquigglyLine
