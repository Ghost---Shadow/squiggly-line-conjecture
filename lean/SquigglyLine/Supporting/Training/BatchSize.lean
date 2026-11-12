/-
Batch size and learning rate.

One set of weights `Θ` and two batches of data, with features `A₁` and `A₂`
and labels `y₁` and `y₂`.

* `gradientStep_two_batches` : a step on the first batch and then a step on
  the second is one step on both at once, minus `η²` times the second batch's
  view of what the first step changed.
* `two_batches_of_cross_kernel_eq_zero` : if the model sees no input of one
  batch as like any input of the other, the two are equal.
* `linear_scaling_rule` : with the push averaged over a batch of size `B`,
  two steps at learning rate `η` are, up to that correction, one step on the
  batch of size `2 B` at learning rate `2 η`.
-/
import SquigglyLine.Supporting.NewInputs.Forgetting

namespace SquigglyLine

open ContinuousLinearMap

variable {Θ Y₁ Y₂ : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Y₁] [InnerProductSpace ℝ Y₁] [CompleteSpace Y₁]
  [NormedAddCommGroup Y₂] [InnerProductSpace ℝ Y₂] [CompleteSpace Y₂]
  (A₁ : Θ →L[ℝ] Y₁) (A₂ : Θ →L[ℝ] Y₂) (y₁ : Y₁) (y₂ : Y₂)

/-- **Two small steps against one big step.** A step on the first batch and then a step on
the second equals one step on both batches at once, minus `η ^ 2` times a term that passes
through the kernel between the batches. -/
theorem gradientStep_two_batches (η : ℝ) (θ : Θ) :
    gradientStep A₂ y₂ η (gradientStep A₁ y₁ η θ)
      = θ + η • (adjoint A₁ (residual (A₁ : Θ →ₗ[ℝ] Y₁) y₁ θ)
            + adjoint A₂ (residual (A₂ : Θ →ₗ[ℝ] Y₂) y₂ θ))
        - η ^ 2 • adjoint A₂ (A₂ (adjoint A₁ (residual (A₁ : Θ →ₗ[ℝ] Y₁) y₁ θ))) := by
  rw [gradientStep, residual_gradientStep_other, map_sub, map_smul, gradientStep]
  module

/-- **When the batches share nothing, the two are equal.** -/
theorem two_batches_of_cross_kernel_eq_zero (hcross : ∀ v, A₂ (adjoint A₁ v) = 0) (η : ℝ)
    (θ : Θ) :
    gradientStep A₂ y₂ η (gradientStep A₁ y₁ η θ)
      = θ + η • (adjoint A₁ (residual (A₁ : Θ →ₗ[ℝ] Y₁) y₁ θ)
            + adjoint A₂ (residual (A₂ : Θ →ₗ[ℝ] Y₂) y₂ θ)) := by
  rw [gradientStep_two_batches, hcross, map_zero, smul_zero, sub_zero]

/-- **The linear scaling rule.** With the push averaged over a batch of size `B`, two steps
at learning rate `η` are one step on the batch of size `2 B` at learning rate `2 η`, minus
the correction, which is of order `η ^ 2`. -/
theorem linear_scaling_rule (η B : ℝ) (θ : Θ) :
    gradientStep A₂ y₂ (η / B) (gradientStep A₁ y₁ (η / B) θ)
      = θ + (2 * η / (2 * B)) • (adjoint A₁ (residual (A₁ : Θ →ₗ[ℝ] Y₁) y₁ θ)
            + adjoint A₂ (residual (A₂ : Θ →ₗ[ℝ] Y₂) y₂ θ))
        - (η / B) ^ 2 • adjoint A₂ (A₂ (adjoint A₁ (residual (A₁ : Θ →ₗ[ℝ] Y₁) y₁ θ))) := by
  rw [gradientStep_two_batches, mul_div_mul_left η B two_ne_zero]

end SquigglyLine
