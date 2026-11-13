/-
Batch size and learning rate.

One set of weights and two batches of data, with features `first_predict` and
`second_predict` and labels `first_labels` and `second_labels`.

* `gradientStep_two_batches` : a step on the first batch and then a step on
  the second is one step on both at once, minus `learning_rate ^ 2` times the
  second batch's view of what the first step changed.
* `two_batches_of_cross_kernel_eq_zero` : if the model sees no input of one
  batch as like any input of the other, the two are equal.
* `linear_scaling_rule` : with the push averaged over a batch of size
  `batch_size`, two steps at learning rate `learning_rate` are, up to that
  correction, one step on the batch of size `2 * batch_size` at learning rate
  `2 * learning_rate`.
-/
import SquigglyLine.Supporting.NewInputs.Forgetting

namespace SquigglyLine

open ContinuousLinearMap

variable {Weights FirstOutputs SecondOutputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup FirstOutputs] [InnerProductSpace ℝ FirstOutputs]
  [CompleteSpace FirstOutputs]
  [NormedAddCommGroup SecondOutputs] [InnerProductSpace ℝ SecondOutputs]
  [CompleteSpace SecondOutputs]
  (first_predict : Weights →L[ℝ] FirstOutputs)
  (second_predict : Weights →L[ℝ] SecondOutputs)
  (first_labels : FirstOutputs) (second_labels : SecondOutputs)

/-- **Two small steps against one big step.** A step on the first batch and
then a step on the second equals one step on both batches at once, minus
`learning_rate ^ 2` times a term that passes through the kernel between the
batches. -/
theorem gradientStep_two_batches
    (learning_rate : ℝ)
    (weights : Weights) :
    let first_linear_predict : LinearPredictor Weights FirstOutputs :=
      first_predict
    let second_linear_predict : LinearPredictor Weights SecondOutputs :=
      second_predict
    let two_steps :=
      TAKE_GRADIENT_STEP second_predict second_labels learning_rate
        (TAKE_GRADIENT_STEP first_predict first_labels learning_rate weights)
    let first_residual :=
      GET_RESIDUAL first_linear_predict first_labels weights
    let second_residual :=
      GET_RESIDUAL second_linear_predict second_labels weights
    let one_big_step :=
      weights + learning_rate • (adjoint first_predict first_residual
        + adjoint second_predict second_residual)
    let correction :=
      learning_rate ^ 2 •
        adjoint second_predict
          (second_predict (adjoint first_predict first_residual))  -- the first step moved the second batch's outputs
    two_steps = one_big_step - correction := by
  unfold_named_pieces
  -- The second step sees the error as the first step left it.
  have step :
      GET_RESIDUAL (second_predict : Weights →ₗ[ℝ] SecondOutputs) second_labels
          (TAKE_GRADIENT_STEP first_predict first_labels learning_rate weights)
        = GET_RESIDUAL (second_predict : Weights →ₗ[ℝ] SecondOutputs)
            second_labels weights
          - learning_rate • second_predict (adjoint first_predict
            (GET_RESIDUAL (first_predict : Weights →ₗ[ℝ] FirstOutputs)
              first_labels weights)) :=
    residual_gradientStep_other second_predict first_predict second_labels
      first_labels learning_rate weights
  rw [TAKE_GRADIENT_STEP, step, map_sub, map_smul, TAKE_GRADIENT_STEP]
  module

/-- **When the batches share nothing, the two are equal.** -/
theorem two_batches_of_cross_kernel_eq_zero
    (cross_kernel_zero : ∀ vector,
      second_predict (adjoint first_predict vector) = 0)
    (learning_rate : ℝ)
    (weights : Weights) :
    let first_linear_predict : LinearPredictor Weights FirstOutputs :=
      first_predict
    let second_linear_predict : LinearPredictor Weights SecondOutputs :=
      second_predict
    let two_steps :=
      TAKE_GRADIENT_STEP second_predict second_labels learning_rate
        (TAKE_GRADIENT_STEP first_predict first_labels learning_rate weights)
    let first_residual :=
      GET_RESIDUAL first_linear_predict first_labels weights
    let second_residual :=
      GET_RESIDUAL second_linear_predict second_labels weights
    let one_big_step :=
      weights + learning_rate • (adjoint first_predict first_residual
        + adjoint second_predict second_residual)
    two_steps = one_big_step := by
  unfold_named_pieces
  have step :
      TAKE_GRADIENT_STEP second_predict second_labels learning_rate
          (TAKE_GRADIENT_STEP first_predict first_labels learning_rate weights)
        = weights + learning_rate • (adjoint first_predict
              (GET_RESIDUAL (first_predict : Weights →ₗ[ℝ] FirstOutputs)
                first_labels weights)
            + adjoint second_predict
              (GET_RESIDUAL (second_predict : Weights →ₗ[ℝ] SecondOutputs)
                second_labels weights))
          - learning_rate ^ 2 • adjoint second_predict (second_predict
            (adjoint first_predict
              (GET_RESIDUAL (first_predict : Weights →ₗ[ℝ] FirstOutputs)
                first_labels weights))) :=
    gradientStep_two_batches first_predict second_predict first_labels
      second_labels learning_rate weights
  rw [step, cross_kernel_zero, map_zero, smul_zero, sub_zero]

/-- **The linear scaling rule.** With the push averaged over a batch of size
`batch_size`, two steps at learning rate `learning_rate` are one step on the
batch of size `2 * batch_size` at learning rate `2 * learning_rate`, minus the
correction, which is of order `learning_rate ^ 2`. -/
theorem linear_scaling_rule
    (learning_rate : ℝ)
    (batch_size : ℝ)
    (weights : Weights) :
    let first_linear_predict : LinearPredictor Weights FirstOutputs :=
      first_predict
    let second_linear_predict : LinearPredictor Weights SecondOutputs :=
      second_predict
    let averaged_rate := learning_rate / batch_size  -- the push is averaged over the batch
    let two_steps :=
      TAKE_GRADIENT_STEP second_predict second_labels averaged_rate
        (TAKE_GRADIENT_STEP first_predict first_labels averaged_rate weights)
    let first_residual :=
      GET_RESIDUAL first_linear_predict first_labels weights
    let second_residual :=
      GET_RESIDUAL second_linear_predict second_labels weights
    let doubled_rate := 2 * learning_rate / (2 * batch_size)  -- twice the batch at twice the rate
    let combined_step :=
      weights + doubled_rate • (adjoint first_predict first_residual
        + adjoint second_predict second_residual)
    let correction :=
      averaged_rate ^ 2 •
        adjoint second_predict
          (second_predict (adjoint first_predict first_residual))
    two_steps = combined_step - correction := by
  unfold_named_pieces
  have step :
      TAKE_GRADIENT_STEP second_predict second_labels (learning_rate / batch_size)
          (TAKE_GRADIENT_STEP first_predict first_labels
            (learning_rate / batch_size) weights)
        = weights + (learning_rate / batch_size) • (adjoint first_predict
              (GET_RESIDUAL (first_predict : Weights →ₗ[ℝ] FirstOutputs)
                first_labels weights)
            + adjoint second_predict
              (GET_RESIDUAL (second_predict : Weights →ₗ[ℝ] SecondOutputs)
                second_labels weights))
          - (learning_rate / batch_size) ^ 2 • adjoint second_predict
            (second_predict (adjoint first_predict
              (GET_RESIDUAL (first_predict : Weights →ₗ[ℝ] FirstOutputs)
                first_labels weights))) :=
    gradientStep_two_batches first_predict second_predict first_labels
      second_labels (learning_rate / batch_size) weights
  rw [step, mul_div_mul_left learning_rate batch_size two_ne_zero]

end SquigglyLine
