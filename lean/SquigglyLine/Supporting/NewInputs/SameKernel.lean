/-
Same kernel, same predictions.

Two models, linear in their weights, with weight spaces `Weights` and
`OtherWeights` that need not be alike. A test point has a feature vector in
each (`features`, `other_features`); the model's answer there is
`⟪features, weights⟫`. The test row of the kernel is `predict features`: how
alike the test point is to each training point.

* `inner_gradientStep` : a gradient step changes the answer at a test point by
  `learning_rate` times the test row matched against the current errors. The
  weights do not appear.
* `prediction_iterate_gradientStep_eq` : so two models with the same kernel,
  the same test row and the same start give the same answer at the test point
  after every step.
* `prediction_kernelFit_eq` : and the same answer at the fit that training
  heads for.

With `residual_iterate_gradientStep_eq` and `travel_eq_of_kernel_eq` this says
a model is its kernel, for training and for prediction.
-/
import SquigglyLine.Networks.Kernel

namespace SquigglyLine

open ContinuousLinearMap

variable {Weights OtherWeights Outputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup OtherWeights] [InnerProductSpace ℝ OtherWeights]
  [CompleteSpace OtherWeights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]

/-- **A step moves a prediction through the kernel only.** The answer at a test
point with features `features` changes by `learning_rate` times the test row
`predict features` matched against the errors. -/
theorem inner_gradientStep
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (weights : Weights)
    (features : Weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let stepped_weights :=
      TAKE_GRADIENT_STEP predict labels learning_rate weights
    let answer_after  := inner ℝ features stepped_weights
    let answer_before := inner ℝ features weights
    let test_row      := predict features  -- how alike the test point is to each training point
    let residual      := GET_RESIDUAL linear_predict labels weights
    let correction    := learning_rate * inner ℝ test_row residual
    answer_after = answer_before + correction := by
  unfold_named_pieces
  rw [TAKE_GRADIENT_STEP, inner_add_right, real_inner_smul_right,
    adjoint_inner_right]

variable {predict : Weights →L[ℝ] Outputs}
  {other_predict : OtherWeights →L[ℝ] Outputs}

/-- **Same kernel, same predictions.** Two models with the same kernel on the
training set, the same test row, the same errors at the start and the same
answer at the test point at the start give the same answer there after every
step of gradient descent. -/
theorem prediction_iterate_gradientStep_eq
    (same_kernel : ∀ vector,
      predict (adjoint predict vector)
        = other_predict (adjoint other_predict vector))
    (labels : Outputs)
    (learning_rate : ℝ)
    {weights : Weights}
    {other_weights : OtherWeights}
    (same_start_residual :
      GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights
        = GET_RESIDUAL (other_predict : OtherWeights →ₗ[ℝ] Outputs) labels
            other_weights)
    {features : Weights}
    {other_features : OtherWeights}
    (same_test_row : predict features = other_predict other_features)
    (same_start_answer :
      inner ℝ features weights = inner ℝ other_features other_weights)
    (step_count : ℕ) :
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count] weights
    let other_trained_weights :=
      (TAKE_GRADIENT_STEP other_predict labels learning_rate)^[step_count]
        other_weights
    let answer       := inner ℝ features trained_weights
    let other_answer := inner ℝ other_features other_trained_weights
    answer = other_answer := by
  unfold_named_pieces
  induction step_count with
  | zero => exact same_start_answer
  | succ previous_count earlier_case =>
    -- Each step adds the same correction to both answers: the test row
    -- matched against the residual, and the residuals stay equal.
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      inner_gradientStep, inner_gradientStep, earlier_case, same_test_row,
      residual_iterate_gradientStep_eq same_kernel labels learning_rate
        same_start_residual previous_count]

/-- **Same kernel, same answer in the end.** The fit
`weights + A† K⁻¹ residual` (the nearest fit, by
`travel_eq_norm_of_kernelInverse`) gives the same answer at the test point in
both models. -/
theorem prediction_kernelFit_eq
    (kernel_inverse : Outputs → Outputs)
    (labels : Outputs)
    {weights : Weights}
    {other_weights : OtherWeights}
    (same_start_residual :
      GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights
        = GET_RESIDUAL (other_predict : OtherWeights →ₗ[ℝ] Outputs) labels
            other_weights)
    {features : Weights}
    {other_features : OtherWeights}
    (same_test_row : predict features = other_predict other_features)
    (same_start_answer :
      inner ℝ features weights = inner ℝ other_features other_weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let other_linear_predict : LinearPredictor OtherWeights Outputs :=
      other_predict
    let fit := weights + adjoint predict
      (kernel_inverse (GET_RESIDUAL linear_predict labels weights))
    let other_fit := other_weights + adjoint other_predict
      (kernel_inverse (GET_RESIDUAL other_linear_predict labels other_weights))
    let answer       := inner ℝ features fit
    let other_answer := inner ℝ other_features other_fit
    answer = other_answer := by
  unfold_named_pieces
  rw [inner_add_right, inner_add_right, adjoint_inner_right,
    adjoint_inner_right, same_start_answer, same_test_row,
    same_start_residual]

end SquigglyLine
