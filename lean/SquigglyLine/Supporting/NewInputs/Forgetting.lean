/-
Catastrophic forgetting: what a new task costs an old one.

One set of weights, two tasks. The old task has features `predict` and labels
`labels`; the new task has features `new_predict` and labels `new_labels`. The
cross kernel is `predict new_predict†`: how alike the model finds the old
inputs and the new ones.

* `residual_gradientStep_other` : a gradient step on the new task changes the
  old errors by `learning_rate` times the cross kernel applied to the new
  errors.
* `inner_forgetting_step` : the same, read along one direction of the old
  labels.
* `residual_iterate_of_cross_kernel_eq_zero` : if the cross kernel is zero,
  training on the new task never changes the old errors.
* `forgetting_le_dist` : moving the weights changes the old errors by at most
  `‖predict‖` times the distance moved.
* `forgetting_le_travel` : so if gradient descent fits the new task, the old
  errors change by at most `‖predict‖` times the new task's travel.
-/
import SquigglyLine.Supporting.Training.LeastAction

namespace SquigglyLine

open ContinuousLinearMap

variable {Weights Outputs NewOutputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]
  [NormedAddCommGroup NewOutputs] [InnerProductSpace ℝ NewOutputs]
  [CompleteSpace NewOutputs]

omit [CompleteSpace Outputs] in
/-- **Forgetting goes through the cross kernel.** A gradient step on the new
task changes the old errors by `learning_rate` times `predict new_predict†`
applied to the new errors. -/
theorem residual_gradientStep_other
    (predict : Weights →L[ℝ] Outputs)
    (new_predict : Weights →L[ℝ] NewOutputs)
    (labels : Outputs)
    (new_labels : NewOutputs)
    (learning_rate : ℝ)
    (weights : Weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let new_linear_predict : LinearPredictor Weights NewOutputs := new_predict
    let stepped_weights :=
      TAKE_GRADIENT_STEP new_predict new_labels learning_rate weights
    let residual_after  := GET_RESIDUAL linear_predict labels stepped_weights
    let residual_before := GET_RESIDUAL linear_predict labels weights
    let new_residual    := GET_RESIDUAL new_linear_predict new_labels weights
    let cross_push      := predict (adjoint new_predict new_residual)  -- the cross kernel applied to the new error
    residual_after = residual_before - learning_rate • cross_push := by
  unfold_named_pieces
  simp only [GET_RESIDUAL, TAKE_GRADIENT_STEP, ContinuousLinearMap.coe_coe,
    map_add, map_smul]
  abel

/-- **Forgetting along one direction.** The old error along `direction`
changes by `learning_rate` times the new task's view of `direction`, matched
against the new errors. -/
theorem inner_forgetting_step
    (predict : Weights →L[ℝ] Outputs)
    (new_predict : Weights →L[ℝ] NewOutputs)
    (labels : Outputs)
    (new_labels : NewOutputs)
    (learning_rate : ℝ)
    (weights : Weights)
    (direction : Outputs) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let new_linear_predict : LinearPredictor Weights NewOutputs := new_predict
    let stepped_weights :=
      TAKE_GRADIENT_STEP new_predict new_labels learning_rate weights
    let error_after :=
      inner ℝ direction (GET_RESIDUAL linear_predict labels stepped_weights)
    let error_before :=
      inner ℝ direction (GET_RESIDUAL linear_predict labels weights)
    let new_residual := GET_RESIDUAL new_linear_predict new_labels weights
    let new_view :=
      inner ℝ (new_predict (adjoint predict direction)) new_residual
    error_after = error_before - learning_rate * new_view := by
  unfold_named_pieces
  have step :
      GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
          (TAKE_GRADIENT_STEP new_predict new_labels learning_rate weights)
        = GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights
          - learning_rate • predict (adjoint new_predict
            (GET_RESIDUAL (new_predict : Weights →ₗ[ℝ] NewOutputs) new_labels
              weights)) :=
    residual_gradientStep_other predict new_predict labels new_labels
      learning_rate weights
  rw [step, inner_sub_right, real_inner_smul_right,
    ← adjoint_inner_left predict, adjoint_inner_right]

omit [CompleteSpace Outputs] in
/-- **Separate features, nothing forgotten.** If the cross kernel is zero, any
number of gradient steps on the new task leave the old errors exactly where
they were. -/
theorem residual_iterate_of_cross_kernel_eq_zero
    (predict : Weights →L[ℝ] Outputs)
    (new_predict : Weights →L[ℝ] NewOutputs)
    (cross_kernel_zero : ∀ vector, predict (adjoint new_predict vector) = 0)
    (labels : Outputs)
    (new_labels : NewOutputs)
    (learning_rate : ℝ)
    (start_weights : Weights)
    (step_count : ℕ) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let trained_weights :=
      (TAKE_GRADIENT_STEP new_predict new_labels learning_rate)^[step_count]
        start_weights
    let residual_after  := GET_RESIDUAL linear_predict labels trained_weights
    let residual_before := GET_RESIDUAL linear_predict labels start_weights
    residual_after = residual_before := by
  unfold_named_pieces
  induction step_count with
  | zero => rfl
  | succ previous_count earlier_case =>
    -- One more step on the new task adds nothing: the cross kernel kills it.
    have step :
        GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
            (TAKE_GRADIENT_STEP new_predict new_labels learning_rate
              ((TAKE_GRADIENT_STEP new_predict new_labels learning_rate)^[
                previous_count] start_weights))
          = GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
              ((TAKE_GRADIENT_STEP new_predict new_labels learning_rate)^[
                previous_count] start_weights)
            - learning_rate • predict (adjoint new_predict
              (GET_RESIDUAL (new_predict : Weights →ₗ[ℝ] NewOutputs)
                new_labels
                ((TAKE_GRADIENT_STEP new_predict new_labels learning_rate)^[
                  previous_count] start_weights))) :=
      residual_gradientStep_other predict new_predict labels new_labels
        learning_rate _
    rw [Function.iterate_succ_apply', step, cross_kernel_zero, smul_zero,
      sub_zero, earlier_case]

omit [CompleteSpace Weights] [CompleteSpace Outputs] in
/-- Moving the weights changes the old errors by at most `‖predict‖` times the
distance moved. -/
theorem forgetting_le_dist
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (weights : Weights)
    (other_weights : Weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let residual_change :=
      ‖GET_RESIDUAL linear_predict labels other_weights
        - GET_RESIDUAL linear_predict labels weights‖
    let weight_distance := ‖other_weights - weights‖
    let ceiling         := ‖predict‖ * weight_distance  -- operator norm: the most `predict` stretches a move
    residual_change ≤ ceiling := by
  unfold_named_pieces
  have residual_diff :
      GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels other_weights
        - GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights
        = -predict (other_weights - weights) := by
    simp only [GET_RESIDUAL, ContinuousLinearMap.coe_coe, map_sub]
    abel
  rw [residual_diff, norm_neg]
  exact predict.le_opNorm _

omit [CompleteSpace Outputs] in
/-- **A ceiling on forgetting.** If gradient descent arrives at a fit of the
new task, the old errors have changed by at most `‖predict‖` times the distance
from the start to the nearest fit of the new task. -/
theorem forgetting_le_travel
    (predict : Weights →L[ℝ] Outputs)
    (new_predict : Weights →L[ℝ] NewOutputs)
    (labels : Outputs)
    (new_labels : NewOutputs)
    (learning_rate : ℝ)
    (start_weights : Weights)
    (step_count : ℕ)
    (new_fit :
      new_predict
        ((TAKE_GRADIENT_STEP new_predict new_labels learning_rate)^[step_count]
          start_weights) = new_labels) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let new_linear_predict : LinearPredictor Weights NewOutputs := new_predict
    let trained_weights :=
      (TAKE_GRADIENT_STEP new_predict new_labels learning_rate)^[step_count]
        start_weights
    let residual_change :=
      ‖GET_RESIDUAL linear_predict labels trained_weights
        - GET_RESIDUAL linear_predict labels start_weights‖
    let new_travel :=
      GET_TRAVEL new_linear_predict new_labels start_weights
    let ceiling := ‖predict‖ * new_travel
    residual_change ≤ ceiling := by
  unfold_named_pieces
  -- Gradient descent arrives at a fit no further than the nearest fit.
  have trained_is_near :
      ‖(TAKE_GRADIENT_STEP new_predict new_labels learning_rate)^[step_count]
          start_weights - start_weights‖
        ≤ GET_TRAVEL (new_predict : Weights →ₗ[ℝ] NewOutputs) new_labels
            start_weights := by
    refine le_csInf ⟨_, _, new_fit, rfl⟩ ?_
    rintro distance ⟨other_weights, other_weights_fit, rfl⟩
    exact gradientDescent_fit_is_nearest new_predict new_labels learning_rate
      start_weights step_count new_fit other_weights_fit
  have change_le :
      ‖GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
          ((TAKE_GRADIENT_STEP new_predict new_labels learning_rate)^[
            step_count] start_weights)
        - GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
            start_weights‖
        ≤ ‖predict‖
          * ‖(TAKE_GRADIENT_STEP new_predict new_labels learning_rate)^[
              step_count] start_weights - start_weights‖ :=
    forgetting_le_dist predict labels start_weights _
  exact change_le.trans
    (mul_le_mul_of_nonneg_left trained_is_near (norm_nonneg predict))

end SquigglyLine
