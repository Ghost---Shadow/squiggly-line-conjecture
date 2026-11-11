/-
Same kernel, same predictions.

Two models, linear in their weights, with weight spaces `Θ` and `Θ'` that need
not be alike. A test point has a feature vector in each (`φ`, `φ'`); the
model's answer there is `⟪φ, θ⟫`. The test row of the kernel is `A φ`: how
alike the test point is to each training point.

* `inner_gradientStep` : a gradient step changes the answer at a test point by
  `η` times the test row matched against the current errors. The weights do
  not appear.
* `prediction_iterate_gradientStep_eq` : so two models with the same kernel,
  the same test row and the same start give the same answer at the test point
  after every step.
* `prediction_kernelFit_eq` : and the same answer at the fit that training
  heads for.

With `residual_iterate_gradientStep_eq` and `travel_eq_of_kernel_eq` this says
a model is its kernel, for training and for prediction.
-/
import SquigglyLine.Kernel

namespace SquigglyLine

open ContinuousLinearMap

variable {Θ Θ' Y : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Θ'] [InnerProductSpace ℝ Θ'] [CompleteSpace Θ']
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- **A step moves a prediction through the kernel only.** The answer at a test point with
features `φ` changes by `η` times the test row `A φ` matched against the errors. -/
theorem inner_gradientStep (A : Θ →L[ℝ] Y) (y : Y) (η : ℝ) (θ φ : Θ) :
    inner ℝ φ (gradientStep A y η θ)
      = inner ℝ φ θ + η * inner ℝ (A φ) (residual (A : Θ →ₗ[ℝ] Y) y θ) := by
  rw [gradientStep, inner_add_right, real_inner_smul_right, adjoint_inner_right]

variable {A : Θ →L[ℝ] Y} {B : Θ' →L[ℝ] Y}

/-- **Same kernel, same predictions.** Two models with the same kernel on the training set,
the same test row, the same errors at the start and the same answer at the test point at the
start give the same answer there after every step of gradient descent. -/
theorem prediction_iterate_gradientStep_eq (hK : ∀ v, A (adjoint A v) = B (adjoint B v))
    (y : Y) (η : ℝ) {θ : Θ} {θ' : Θ'}
    (h : residual (A : Θ →ₗ[ℝ] Y) y θ = residual (B : Θ' →ₗ[ℝ] Y) y θ')
    {φ : Θ} {φ' : Θ'} (hrow : A φ = B φ') (hstart : inner ℝ φ θ = inner ℝ φ' θ') (t : ℕ) :
    inner ℝ φ ((gradientStep A y η)^[t] θ) = inner ℝ φ' ((gradientStep B y η)^[t] θ') := by
  induction t with
  | zero => exact hstart
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', inner_gradientStep,
      inner_gradientStep, ih, hrow, residual_iterate_gradientStep_eq hK y η h n]

/-- **Same kernel, same answer in the end.** The fit `θ + A† K⁻¹ r` (the nearest fit, by
`travel_eq_norm_of_kernelInverse`) gives the same answer at the test point in both models. -/
theorem prediction_kernelFit_eq (Kinv : Y → Y) (y : Y) {θ : Θ} {θ' : Θ'}
    (h : residual (A : Θ →ₗ[ℝ] Y) y θ = residual (B : Θ' →ₗ[ℝ] Y) y θ')
    {φ : Θ} {φ' : Θ'} (hrow : A φ = B φ') (hstart : inner ℝ φ θ = inner ℝ φ' θ') :
    inner ℝ φ (θ + adjoint A (Kinv (residual (A : Θ →ₗ[ℝ] Y) y θ)))
      = inner ℝ φ' (θ' + adjoint B (Kinv (residual (B : Θ' →ₗ[ℝ] Y) y θ'))) := by
  rw [inner_add_right, inner_add_right, adjoint_inner_right, adjoint_inner_right, hstart, hrow, h]

end SquigglyLine
