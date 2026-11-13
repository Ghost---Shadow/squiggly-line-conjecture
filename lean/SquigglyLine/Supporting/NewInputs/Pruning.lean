/-
Lottery tickets: what pruning costs.

Split a model's weights into the kept ones (features `kept_predict`) and the
dropped ones (features `dropped_predict`). The whole model `whole_predict` has
both. Its kernel is the sum of the two kernels (`IS_KERNEL_SUM`).

* `kernel_eigen_add` : along a direction where the kept weights have strength
  `kept_strength` and the dropped weights have strength `dropped_strength`, the
  whole model has strength `kept_strength + dropped_strength`.
* `pruned_share_ge` : the pruned model has at least as large a share of its
  error left along that direction, at every step.
* `winning_ticket` : if the dropped weights have no strength along a
  direction, the pruned model and the whole model keep the same error there
  at every step.
* `travel_mul_sqrt_pruned` : with orthogonal features of strengths
  `kept_strength` and `dropped_strength`, pruning moves the nearest fit farther
  by `√((kept_strength + dropped_strength) / kept_strength)`.

Definition and theorems:

* `IS_KERNEL_SUM`                  the whole kernel is the sum of the two;
* `kernel_eigen_add`               strengths add;
* `pruned_share_ge`                pruning slows a direction down;
* `winning_ticket`                 no strength dropped, no error added;
* `HAS_TIGHT_FEATURES.of_kernelSum`  orthogonal features add up;
* `travel_mul_sqrt_pruned`         pruning moves the fit farther.
-/
import SquigglyLine.Supporting.Training.SpectralBias

namespace SquigglyLine

open ContinuousLinearMap

variable {KeptWeights DroppedWeights WholeWeights Outputs : Type*}
  [NormedAddCommGroup KeptWeights] [InnerProductSpace ℝ KeptWeights]
  [CompleteSpace KeptWeights]
  [NormedAddCommGroup DroppedWeights] [InnerProductSpace ℝ DroppedWeights]
  [CompleteSpace DroppedWeights]
  [NormedAddCommGroup WholeWeights] [InnerProductSpace ℝ WholeWeights]
  [CompleteSpace WholeWeights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]

/-- The whole model `whole_predict` has the kept features `kept_predict` and the
dropped features `dropped_predict` side by side: its kernel is the sum of their
kernels. -/
def IS_KERNEL_SUM
    (whole_predict : WholeWeights →L[ℝ] Outputs)
    (kept_predict : KeptWeights →L[ℝ] Outputs)
    (dropped_predict : DroppedWeights →L[ℝ] Outputs) : Prop :=
  ∀ vector, whole_predict (adjoint whole_predict vector)
    = kept_predict (adjoint kept_predict vector)
      + dropped_predict (adjoint dropped_predict vector)

variable {whole_predict : WholeWeights →L[ℝ] Outputs}
  {kept_predict : KeptWeights →L[ℝ] Outputs}
  {dropped_predict : DroppedWeights →L[ℝ] Outputs}

/-- **Strengths add.** -/
theorem kernel_eigen_add
    (kernel_is_sum : IS_KERNEL_SUM whole_predict kept_predict dropped_predict)
    {direction : Outputs}
    {kept_strength : ℝ}
    {dropped_strength : ℝ}
    (kept_stretches :
      kept_predict (adjoint kept_predict direction)
        = kept_strength • direction)
    (dropped_stretches :
      dropped_predict (adjoint dropped_predict direction)
        = dropped_strength • direction) :
    let whole_strength := kept_strength + dropped_strength
    let whole_kernel   := whole_predict (adjoint whole_predict direction)
    let stretched      := whole_strength • direction
    whole_kernel = stretched := by
  unfold_named_pieces
  rw [kernel_is_sum direction, kept_stretches, dropped_stretches, add_smul]

/-- **Pruning slows a direction down.** With step size `learning_rate`, the
share of the error left along a direction is at least as large for the pruned
model as for the whole model. -/
theorem pruned_share_ge
    {learning_rate : ℝ}
    {kept_strength : ℝ}
    {dropped_strength : ℝ}
    (learning_rate_nonneg : 0 ≤ learning_rate)
    (dropped_strength_nonneg : 0 ≤ dropped_strength)
    (whole_rate_le_one :
      learning_rate * (kept_strength + dropped_strength) ≤ 1)
    (step_count : ℕ) :
    let whole_strength := kept_strength + dropped_strength
    let whole_share    := (1 - learning_rate * whole_strength) ^ step_count
    let pruned_share   := (1 - learning_rate * kept_strength) ^ step_count
    whole_share ≤ pruned_share := by
  unfold_named_pieces
  -- The whole model is the stronger one: its strength has `dropped_strength`
  -- added.
  exact strong_directions_first (weak_strength := kept_strength)
    learning_rate_nonneg (by linarith) whole_rate_le_one step_count

/-- **A winning ticket.** If the dropped weights have no strength along
`direction`, then the pruned model and the whole model, started with the same
error along `direction`, keep the same error along `direction` at every step of
gradient descent. -/
theorem winning_ticket
    (kernel_is_sum : IS_KERNEL_SUM whole_predict kept_predict dropped_predict)
    (labels : Outputs)
    (learning_rate : ℝ)
    {direction : Outputs}
    {kept_strength : ℝ}
    (kept_stretches :
      kept_predict (adjoint kept_predict direction)
        = kept_strength • direction)
    (dropped_kills_direction :
      dropped_predict (adjoint dropped_predict direction) = 0)
    {kept_weights : KeptWeights}
    {whole_weights : WholeWeights}
    (same_start_error :
      inner ℝ direction
          (GET_RESIDUAL (kept_predict : KeptWeights →ₗ[ℝ] Outputs) labels
            kept_weights)
        = inner ℝ direction
          (GET_RESIDUAL (whole_predict : WholeWeights →ₗ[ℝ] Outputs) labels
            whole_weights))
    (step_count : ℕ) :
    let kept_linear : LinearPredictor KeptWeights Outputs := kept_predict
    let whole_linear : LinearPredictor WholeWeights Outputs := whole_predict
    let kept_trained  :=
      (TAKE_GRADIENT_STEP kept_predict labels learning_rate)^[step_count]
        kept_weights
    let whole_trained :=
      (TAKE_GRADIENT_STEP whole_predict labels learning_rate)^[step_count]
        whole_weights
    let kept_error  := inner ℝ direction
      (GET_RESIDUAL kept_linear labels kept_trained)
    let whole_error := inner ℝ direction
      (GET_RESIDUAL whole_linear labels whole_trained)
    kept_error = whole_error := by
  unfold_named_pieces
  -- The dropped weights add nothing along `direction`, so the whole model
  -- stretches it by the same `kept_strength`.
  have whole_stretches :
      whole_predict (adjoint whole_predict direction)
        = kept_strength • direction := by
    rw [kernel_is_sum direction, kept_stretches, dropped_kills_direction,
      add_zero]
  have kept_formula :
      inner ℝ direction
          (GET_RESIDUAL (kept_predict : KeptWeights →ₗ[ℝ] Outputs) labels
            ((TAKE_GRADIENT_STEP kept_predict labels learning_rate)^[step_count]
              kept_weights))
        = (1 - learning_rate * kept_strength) ^ step_count
          * inner ℝ direction
            (GET_RESIDUAL (kept_predict : KeptWeights →ₗ[ℝ] Outputs) labels
              kept_weights) :=
    inner_residual_iterate_gradientStep kept_predict labels learning_rate
      kept_weights kept_stretches step_count
  have whole_formula :
      inner ℝ direction
          (GET_RESIDUAL (whole_predict : WholeWeights →ₗ[ℝ] Outputs) labels
            ((TAKE_GRADIENT_STEP whole_predict labels learning_rate)^[step_count]
              whole_weights))
        = (1 - learning_rate * kept_strength) ^ step_count
          * inner ℝ direction
            (GET_RESIDUAL (whole_predict : WholeWeights →ₗ[ℝ] Outputs) labels
              whole_weights) :=
    inner_residual_iterate_gradientStep whole_predict labels learning_rate
      whole_weights whole_stretches step_count
  rw [kept_formula, whole_formula, same_start_error]

/-- With orthogonal features on both sides, the whole model has orthogonal
features too, and the strengths add. -/
theorem HAS_TIGHT_FEATURES.of_kernelSum
    (kernel_is_sum : IS_KERNEL_SUM whole_predict kept_predict dropped_predict)
    {kept_strength : ℝ}
    {dropped_strength : ℝ}
    (kept_tight : HAS_TIGHT_FEATURES kept_predict kept_strength)
    (dropped_tight : HAS_TIGHT_FEATURES dropped_predict dropped_strength) :
    let whole_strength := kept_strength + dropped_strength
    HAS_TIGHT_FEATURES whole_predict whole_strength := by
  unfold_named_pieces
  intro vector
  rw [kernel_is_sum vector, kept_tight vector, dropped_tight vector, add_smul]

/-- **Pruning moves the fit farther.** With orthogonal features of strengths
`kept_strength` (kept) and `dropped_strength` (dropped), and the same error at
the start, the travel of the pruned model times `√kept_strength` is the travel
of the whole model times `√(kept_strength + dropped_strength)`. -/
theorem travel_mul_sqrt_pruned
    (kernel_is_sum : IS_KERNEL_SUM whole_predict kept_predict dropped_predict)
    {kept_strength : ℝ}
    {dropped_strength : ℝ}
    (kept_strength_pos : 0 < kept_strength)
    (dropped_strength_nonneg : 0 ≤ dropped_strength)
    (kept_tight : HAS_TIGHT_FEATURES kept_predict kept_strength)
    (dropped_tight : HAS_TIGHT_FEATURES dropped_predict dropped_strength)
    (labels : Outputs)
    {kept_weights : KeptWeights}
    {whole_weights : WholeWeights}
    (same_start_residual :
      GET_RESIDUAL (kept_predict : KeptWeights →ₗ[ℝ] Outputs) labels
          kept_weights
        = GET_RESIDUAL (whole_predict : WholeWeights →ₗ[ℝ] Outputs) labels
          whole_weights) :
    let kept_linear : LinearPredictor KeptWeights Outputs := kept_predict
    let whole_linear : LinearPredictor WholeWeights Outputs := whole_predict
    let whole_strength := kept_strength + dropped_strength
    let kept_travel    := GET_TRAVEL kept_linear labels kept_weights
    let whole_travel   := GET_TRAVEL whole_linear labels whole_weights
    let pruned_side    := kept_travel * √kept_strength
    let whole_side     := whole_travel * √whole_strength  -- travel is error over `√strength`
    pruned_side = whole_side := by
  unfold_named_pieces
  have whole_strength_pos : 0 < kept_strength + dropped_strength := by
    linarith
  have whole_tight :
      HAS_TIGHT_FEATURES whole_predict (kept_strength + dropped_strength) :=
    HAS_TIGHT_FEATURES.of_kernelSum kernel_is_sum kept_tight dropped_tight
  rw [kept_tight.travel_eq kept_strength_pos,
    whole_tight.travel_eq whole_strength_pos, same_start_residual,
    div_mul_cancel₀ _ (Real.sqrt_pos.mpr kept_strength_pos).ne',
    div_mul_cancel₀ _ (Real.sqrt_pos.mpr whole_strength_pos).ne']

end SquigglyLine
