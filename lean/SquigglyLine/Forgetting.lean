/-
Catastrophic forgetting: what a new task costs an old one.

One set of weights `Θ`, two tasks. The old task has features `A` and labels
`y`; the new task has features `B` and labels `z`. The cross kernel is
`A B†`: how alike the model finds the old inputs and the new ones.

* `residual_gradientStep_other` : a gradient step on the new task changes the
  old errors by `η` times the cross kernel applied to the new errors.
* `inner_forgetting_step` : the same, read along one direction of the old
  labels.
* `residual_iterate_of_cross_kernel_eq_zero` : if the cross kernel is zero,
  training on the new task never changes the old errors.
* `forgetting_le_dist` : moving the weights changes the old errors by at most
  `‖A‖` times the distance moved.
* `forgetting_le_travel` : so if gradient descent fits the new task, the old
  errors change by at most `‖A‖` times the new task's travel.
-/
import SquigglyLine.LeastAction

namespace SquigglyLine

open ContinuousLinearMap

variable {Θ Y Z : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]

omit [CompleteSpace Y] in
/-- **Forgetting goes through the cross kernel.** A gradient step on the new task changes
the old errors by `η` times `A B†` applied to the new errors. -/
theorem residual_gradientStep_other (A : Θ →L[ℝ] Y) (B : Θ →L[ℝ] Z) (y : Y) (z : Z) (η : ℝ)
    (θ : Θ) :
    residual (A : Θ →ₗ[ℝ] Y) y (gradientStep B z η θ)
      = residual (A : Θ →ₗ[ℝ] Y) y θ
        - η • A (adjoint B (residual (B : Θ →ₗ[ℝ] Z) z θ)) := by
  simp only [residual, gradientStep, ContinuousLinearMap.coe_coe, map_add, map_smul]
  abel

/-- **Forgetting along one direction.** The old error along `u` changes by `η` times the
new task's view of `u`, matched against the new errors. -/
theorem inner_forgetting_step (A : Θ →L[ℝ] Y) (B : Θ →L[ℝ] Z) (y : Y) (z : Z) (η : ℝ) (θ : Θ)
    (u : Y) :
    inner ℝ u (residual (A : Θ →ₗ[ℝ] Y) y (gradientStep B z η θ))
      = inner ℝ u (residual (A : Θ →ₗ[ℝ] Y) y θ)
        - η * inner ℝ (B (adjoint A u)) (residual (B : Θ →ₗ[ℝ] Z) z θ) := by
  rw [residual_gradientStep_other, inner_sub_right, real_inner_smul_right,
    ← adjoint_inner_left A, adjoint_inner_right]

omit [CompleteSpace Y] in
/-- **Separate features, nothing forgotten.** If the cross kernel is zero, any number of
gradient steps on the new task leave the old errors exactly where they were. -/
theorem residual_iterate_of_cross_kernel_eq_zero (A : Θ →L[ℝ] Y) (B : Θ →L[ℝ] Z)
    (hcross : ∀ v, A (adjoint B v) = 0) (y : Y) (z : Z) (η : ℝ) (θ₀ : Θ) (t : ℕ) :
    residual (A : Θ →ₗ[ℝ] Y) y ((gradientStep B z η)^[t] θ₀)
      = residual (A : Θ →ₗ[ℝ] Y) y θ₀ := by
  induction t with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', residual_gradientStep_other, hcross, smul_zero, sub_zero,
      ih]

omit [CompleteSpace Θ] [CompleteSpace Y] in
/-- Moving the weights changes the old errors by at most `‖A‖` times the distance moved. -/
theorem forgetting_le_dist (A : Θ →L[ℝ] Y) (y : Y) (θ θ' : Θ) :
    ‖residual (A : Θ →ₗ[ℝ] Y) y θ' - residual (A : Θ →ₗ[ℝ] Y) y θ‖ ≤ ‖A‖ * ‖θ' - θ‖ := by
  have hdiff : residual (A : Θ →ₗ[ℝ] Y) y θ' - residual (A : Θ →ₗ[ℝ] Y) y θ = -A (θ' - θ) := by
    simp only [residual, ContinuousLinearMap.coe_coe, map_sub]
    abel
  rw [hdiff, norm_neg]
  exact A.le_opNorm _

omit [CompleteSpace Y] in
/-- **A ceiling on forgetting.** If gradient descent arrives at a fit of the new task, the
old errors have changed by at most `‖A‖` times the distance from the start to the nearest
fit of the new task. -/
theorem forgetting_le_travel (A : Θ →L[ℝ] Y) (B : Θ →L[ℝ] Z) (y : Y) (z : Z) (η : ℝ) (θ₀ : Θ)
    (t : ℕ) (hfit : B ((gradientStep B z η)^[t] θ₀) = z) :
    ‖residual (A : Θ →ₗ[ℝ] Y) y ((gradientStep B z η)^[t] θ₀)
        - residual (A : Θ →ₗ[ℝ] Y) y θ₀‖
      ≤ ‖A‖ * travel (B : Θ →ₗ[ℝ] Z) z θ₀ := by
  have hnear : ‖(gradientStep B z η)^[t] θ₀ - θ₀‖ ≤ travel (B : Θ →ₗ[ℝ] Z) z θ₀ := by
    refine le_csInf ⟨_, _, hfit, rfl⟩ ?_
    rintro d ⟨θ', hθ', rfl⟩
    exact gradientDescent_fit_is_nearest B z η θ₀ t hfit hθ'
  exact (forgetting_le_dist A y θ₀ _).trans (mul_le_mul_of_nonneg_left hnear (norm_nonneg A))

end SquigglyLine
