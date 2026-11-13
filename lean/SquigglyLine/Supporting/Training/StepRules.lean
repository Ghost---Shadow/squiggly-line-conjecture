/-
Rules for the step: Adam, clipping, a subspace, rounding.

Plain gradient descent takes a step in proportion to the gradient. These are
four other rules in common use, each read as a statement about travel.

| Name                | Meaning                                              |
|---------------------|------------------------------------------------------|
| `TAKE_ADAM_STEP`    | one coordinate of an Adam step with no memory        |
| `CLIP`              | a gradient cut down to a given length                |
| `GradientPerStep`   | one gradient for each step of training               |

Adam with no memory (`TAKE_ADAM_STEP`), one coordinate at a time:
* `adamStep_eq_sign` : the step is the sign of the gradient.
* `adamStep_mul` : multiplying the loss by a positive number changes nothing.
* `abs_adamStep` : every coordinate with a gradient moves the same distance.
* `abs_sub_signStep` : so a gap closes by exactly `learning_rate` per step,
  whatever the strength of the direction.

Gradient clipping (`CLIP`):
* `norm_clip_le` : a clipped gradient is no longer than the limit.
* `clip_of_norm_le` : a gradient within the limit is left alone.
* `norm_sum_clip_le` : so `step_count` steps travel at most
  `step_count * |learning_rate| * limit`.

Training inside a subspace:
* `travel_le_travel_comp` : weights confined to a subspace never have a
  shorter trip to a fit.

Rounding the weights:
* `liftedModel_add` : the model is additive in its weights.
* `abs_liftedModel_add_sub_le` : moving the weights by `weight_change` moves
  each output by at most `‖weight_change‖` times the size of the features.
* `lipschitzWith_liftedModel_add_sub` : and changes the slope by at most
  `‖weight_change‖` times the stretch of the lift.
-/
import Mathlib.Analysis.Real.Sqrt
import SquigglyLine.Networks.Lift
import SquigglyLine.Networks.LinearModel

namespace SquigglyLine

open NNReal

/-- One gradient for each step of training.
Python: `list[Vector]`. -/
abbrev GradientPerStep (Weights : Type*) := ℕ → Weights

/-! ### Adam with no memory -/

section Adam

/-- One coordinate of an Adam step with no memory of earlier steps: the
gradient divided by its own size.
Python: `gradient / sqrt(gradient ** 2)`. -/
noncomputable def TAKE_ADAM_STEP
    (gradient : ℝ) : ℝ :=
  gradient / √(gradient ^ 2)

/-- **The step is the sign of the gradient.** -/
theorem adamStep_eq_sign
    (gradient : ℝ) :
    let step          := TAKE_ADAM_STEP gradient
    let gradient_sign : ℝ := SignType.sign gradient  -- minus one, zero or one
    step = gradient_sign := by
  unfold_named_pieces
  -- `√(gradient²)` is the size of the gradient; split on its sign.
  rw [TAKE_ADAM_STEP, Real.sqrt_sq_eq_abs]
  rcases lt_trichotomy gradient 0 with negative | rfl | positive
  · rw [abs_of_neg negative, sign_neg negative, div_neg,
      div_self negative.ne]
    simp
  · simp
  · rw [abs_of_pos positive, sign_pos positive, div_self positive.ne']
    simp

/-- **Multiplying the loss by a positive number changes nothing.** -/
theorem adamStep_mul
    {scale : ℝ}
    (scale_pos : 0 < scale)
    (gradient : ℝ) :
    let scaled_step := TAKE_ADAM_STEP (scale * gradient)
    let step        := TAKE_ADAM_STEP gradient
    scaled_step = step := by
  unfold_named_pieces
  have step_is_sign (value : ℝ) :
      TAKE_ADAM_STEP value = SignType.sign value :=
    adamStep_eq_sign value
  -- Both steps are signs, and a positive scale does not change a sign.
  rw [step_is_sign, step_is_sign, sign_mul, sign_pos scale_pos, one_mul]

/-- **Every coordinate with a gradient moves the same distance.** -/
theorem abs_adamStep
    {gradient : ℝ}
    (gradient_ne_zero : gradient ≠ 0) :
    let step_size := |TAKE_ADAM_STEP gradient|
    step_size = 1 := by  -- the sign of a non-zero number is plus or minus one
  unfold_named_pieces
  rw [TAKE_ADAM_STEP, Real.sqrt_sq_eq_abs, abs_div, abs_abs,
    div_self (abs_ne_zero.mpr gradient_ne_zero)]

/-- **A gap closes by `learning_rate` per step, whatever the strength.** A
coordinate is off by `gap`. A step of size `learning_rate` against the sign of
the error leaves it off by `|gap| - learning_rate`. The strength of the
direction does not appear. -/
theorem abs_sub_signStep
    {gap : ℝ}
    {learning_rate : ℝ}
    (learning_rate_nonneg : 0 ≤ learning_rate)
    (learning_rate_le_gap : learning_rate ≤ |gap|) :
    let step : ℝ       := learning_rate * SignType.sign gap
    let remaining_gap  := |gap - step|
    let closed_gap     := |gap| - learning_rate  -- the step is `learning_rate` long, aimed at zero
    remaining_gap = closed_gap := by
  unfold_named_pieces
  -- Split on which side of zero the gap lies.
  rcases lt_trichotomy gap 0 with negative | rfl | positive
  · have rate_le_neg_gap : learning_rate ≤ -gap := by
      rwa [abs_of_neg negative] at learning_rate_le_gap
    rw [sign_neg negative, abs_of_neg negative]
    simp only [SignType.coe_neg_one, mul_neg, mul_one, sub_neg_eq_add]
    rw [abs_of_nonpos (by linarith)]
    ring
  · have rate_is_zero : learning_rate = 0 :=
      le_antisymm (by simpa using learning_rate_le_gap)
        learning_rate_nonneg
    simp [rate_is_zero]
  · have rate_le_gap : learning_rate ≤ gap := by
      rwa [abs_of_pos positive] at learning_rate_le_gap
    rw [sign_pos positive, abs_of_pos positive]
    simp only [SignType.coe_one, mul_one]
    rw [abs_of_nonneg (by linarith)]

end Adam

/-! ### Gradient clipping -/

section Clip

variable {Weights : Type*}
  [NormedAddCommGroup Weights] [NormedSpace ℝ Weights]

/-- Clip a gradient to length at most `limit`, keeping its direction.
Python: `min(1, limit / norm(gradient)) * gradient`. -/
noncomputable def CLIP
    (limit : ℝ)
    (gradient : Weights) : Weights :=
  min 1 (limit / ‖gradient‖) • gradient

/-- **A clipped gradient is no longer than the limit.** -/
theorem norm_clip_le
    {limit : ℝ}
    (limit_nonneg : 0 ≤ limit)
    (gradient : Weights) :
    let clipped        := CLIP limit gradient
    let clipped_length := ‖clipped‖
    clipped_length ≤ limit := by
  unfold_named_pieces
  rcases eq_or_ne gradient 0 with rfl | gradient_ne_zero
  · simpa [CLIP] using limit_nonneg
  have length_pos : 0 < ‖gradient‖ := norm_pos_iff.mpr gradient_ne_zero
  rw [CLIP, norm_smul,
    Real.norm_of_nonneg
      (le_min zero_le_one (div_nonneg limit_nonneg length_pos.le))]
  -- The scale is at most `limit / ‖gradient‖`, which makes the length at
  -- most `limit`.
  calc min 1 (limit / ‖gradient‖) * ‖gradient‖
      ≤ limit / ‖gradient‖ * ‖gradient‖ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) length_pos.le
    _ = limit := div_mul_cancel₀ limit length_pos.ne'

/-- A gradient within the limit is left alone. -/
theorem clip_of_norm_le
    {limit : ℝ}
    {gradient : Weights}
    (gradient_ne_zero : gradient ≠ 0)
    (gradient_within_limit : ‖gradient‖ ≤ limit) :
    let clipped := CLIP limit gradient
    clipped = gradient := by
  unfold_named_pieces
  rw [CLIP,
    min_eq_left
      ((one_le_div (norm_pos_iff.mpr gradient_ne_zero)).mpr
        gradient_within_limit),
    one_smul]

/-- **Clipping caps the travel.** After `step_count` steps of size
`learning_rate` with gradients clipped to `limit`, the weights have moved at
most `step_count * |learning_rate| * limit`, whatever the gradients were. -/
theorem norm_sum_clip_le
    {limit : ℝ}
    (limit_nonneg : 0 ≤ limit)
    (gradients : GradientPerStep Weights)
    (learning_rate : ℝ)
    (step_count : ℕ) :
    let total_move : Weights :=
      ∑ k ∈ Finset.range step_count,
        learning_rate • CLIP limit (gradients k)  -- the steps added up, one per training step
    let travel      := ‖total_move‖
    let travel_cap : ℝ := step_count * (|learning_rate| * limit)  -- each step moves at most `|learning_rate| * limit`
    travel ≤ travel_cap := by
  unfold_named_pieces
  -- The triangle inequality, then the cap on each step.
  calc ‖∑ k ∈ Finset.range step_count,
        learning_rate • CLIP limit (gradients k)‖
      ≤ ∑ k ∈ Finset.range step_count,
          ‖learning_rate • CLIP limit (gradients k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range step_count, |learning_rate| * limit :=
        Finset.sum_le_sum fun k _ => by
          rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left
            (norm_clip_le limit_nonneg _) (abs_nonneg _)
    _ = step_count * (|learning_rate| * limit) := by simp

end Clip

/-! ### Training inside a subspace -/

section Subspace

variable {Weights SubWeights Outputs : Type*}
  [NormedAddCommGroup Weights] [NormedSpace ℝ Weights]
  [NormedAddCommGroup SubWeights] [NormedSpace ℝ SubWeights]
  [NormedAddCommGroup Outputs] [NormedSpace ℝ Outputs]

/-- **Confining the weights never shortens the trip.** Let the weights move
only inside a subspace, given by a map `embed` that keeps lengths. If a fit
exists there, it is at least as far from the start as the nearest fit of the
full model. -/
theorem travel_le_travel_comp
    (predict : LinearPredictor Weights Outputs)
    (embed : LinearPredictor SubWeights Weights)
    (embed_keeps_length : ∀ change, ‖embed change‖ = ‖change‖)
    (labels : Outputs)
    (start_weights : SubWeights)
    (some_weights_fit : ∃ weights, predict (embed weights) = labels) :
    let travel_of_full_model :=
      GET_TRAVEL predict labels (embed start_weights)
    let travel_in_subspace   :=
      GET_TRAVEL (predict ∘ₗ embed) labels start_weights
    travel_of_full_model ≤ travel_in_subspace := by
  unfold_named_pieces
  -- Every distance inside the subspace is also a distance of the full model,
  -- since `embed` keeps lengths. So the full model's nearest fit is nearer.
  refine csInf_le_csInf ⟨0, ?_⟩ ?_ ?_
  · rintro distance ⟨weights, -, rfl⟩
    exact norm_nonneg _
  · obtain ⟨weights, weights_fit⟩ := some_weights_fit
    exact ⟨_, weights, weights_fit, rfl⟩
  · rintro distance ⟨weights, weights_fit, rfl⟩
    exact ⟨embed weights, weights_fit, by rw [← map_sub, embed_keeps_length]⟩

end Subspace

/-! ### Rounding the weights -/

section Rounding

variable {Inputs Weights : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]

/-- The model is additive in its weights: the output for summed weights is
the sum of the outputs. -/
theorem liftedModel_add
    (features : FeatureMap Inputs Weights)
    (weights : Weights)
    (weight_change : Weights)
    (input : Inputs) :
    let new_output    :=
      EVALUATE_LIFTED_MODEL features (weights + weight_change) input
    let old_output    := EVALUATE_LIFTED_MODEL features weights input
    let output_change := EVALUATE_LIFTED_MODEL features weight_change input
    new_output = old_output + output_change := by
  unfold_named_pieces
  exact inner_add_left _ _ _

/-- **Rounding moves each output by at most the rounding error times the size
of the features.** -/
theorem abs_liftedModel_add_sub_le
    (features : FeatureMap Inputs Weights)
    (weights : Weights)
    (weight_change : Weights)
    (input : Inputs) :
    let new_output       :=
      EVALUATE_LIFTED_MODEL features (weights + weight_change) input
    let old_output       := EVALUATE_LIFTED_MODEL features weights input
    let change_in_output := |new_output - old_output|
    let rounding_error   := ‖weight_change‖
    let feature_size     := ‖features input‖
    change_in_output ≤ rounding_error * feature_size := by
  unfold_named_pieces
  have add_split :
      EVALUATE_LIFTED_MODEL features (weights + weight_change) input
        = EVALUATE_LIFTED_MODEL features weights input
          + EVALUATE_LIFTED_MODEL features weight_change input :=
    liftedModel_add features weights weight_change input
  -- The extra output is one dot product, of the change with the features.
  rw [add_split, add_sub_cancel_left]
  exact abs_real_inner_le_norm _ _

/-- **Rounding changes the slope by at most the rounding error times the
stretch of the lift.** -/
theorem lipschitzWith_liftedModel_add_sub
    [PseudoMetricSpace Inputs]
    {features : FeatureMap Inputs Weights}
    {lift_slope_limit : SlopeLimit}
    (lift_slope_is_bounded : LipschitzWith lift_slope_limit features)
    (weights : Weights)
    (weight_change : Weights) :
    let slope_limit := ‖weight_change‖₊ * lift_slope_limit  -- tilt of the change times stretch of the lift
    LipschitzWith slope_limit fun input =>
      EVALUATE_LIFTED_MODEL features (weights + weight_change) input
        - EVALUATE_LIFTED_MODEL features weights input := by
  unfold_named_pieces
  have add_split (point : Inputs) :
      EVALUATE_LIFTED_MODEL features (weights + weight_change) point
        = EVALUATE_LIFTED_MODEL features weights point
          + EVALUATE_LIFTED_MODEL features weight_change point :=
    liftedModel_add features weights weight_change point
  -- The old output cancels, leaving the model of the change alone.
  simp only [add_split, add_sub_cancel_left]
  exact lipschitzWith_liftedModel lift_slope_is_bounded weight_change

end Rounding

end SquigglyLine
