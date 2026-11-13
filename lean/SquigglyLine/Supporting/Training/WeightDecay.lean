/-
Weight decay, early stopping and spare parameters are one thing.

Follow a direction of the labels that the kernel stretches by
`kernel_strength`. Weight decay adds a penalty `decay_strength` on the distance
of the weights from their start.

* `residual_ridgeFit` : the weight-decay fit leaves the share
  `decay_strength / (kernel_strength + decay_strength)` of the error.
* `ridge_stationary`, `decayStep_ridgeFit` : it is where gradient descent
  with weight decay comes to rest.
* `inner_ridgeFit` : it moves the answer at a new input by the overlap divided
  by `kernel_strength + decay_strength`. This is the benign-overfitting formula
  with the strength of the dropped features equal to `decay_strength`.
* `early_stopping_le_ridge` : stopping after `step_count` steps leaves at most
  `1 / (1 + step_count * rate)` of the error, where
  `rate = learning_rate * kernel_strength`.
* `ridge_share_eq` : and that is the share weight decay leaves when
  `decay_strength = 1 / (learning_rate * step_count)`.

Definitions and theorems:

* `GET_RIDGE_FIT`          the fit that weight decay rests at;
* `TAKE_DECAY_STEP`        one step of gradient descent with weight decay;
* `early_stopping_le_ridge`  early stopping cuts at least as hard;
* `ridge_share_eq`         the matching penalty;
* `residual_ridgeFit`      what weight decay leaves;
* `ridge_stationary`       the resting point;
* `decayStep_ridgeFit`     gradient descent with weight decay rests there;
* `inner_ridgeFit`         weight decay is spare parameters.
-/
import Mathlib.Tactic.LinearCombination
import SquigglyLine.Supporting.Training.SpectralBias

namespace SquigglyLine

/-! ### The share of the error left -/

section Share

/-- **Early stopping cuts at least as hard as weight decay.** After
`step_count` steps at rate `rate` the share of the error left is at most
`1 / (1 + step_count * rate)`. -/
theorem early_stopping_le_ridge
    {rate : ℝ}
    (rate_nonneg : 0 ≤ rate)
    (rate_le_one : rate ≤ 1)
    (step_count : ℕ) :
    let stopped_share := (1 - rate) ^ step_count
    let ridge_share   := 1 / (1 + step_count * rate)
    stopped_share ≤ ridge_share := by
  unfold_named_pieces
  have exponent_nonneg : 0 ≤ (step_count : ℝ) * rate :=
    mul_nonneg (Nat.cast_nonneg step_count) rate_nonneg
  -- `1 - rate` is at most `exp (-rate)`, and `exp x` is at least `1 + x`.
  calc (1 - rate) ^ step_count ≤ Real.exp (-(step_count * rate)) :=
        pow_one_sub_le_exp rate_le_one step_count
    _ = 1 / Real.exp (step_count * rate) := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / (1 + step_count * rate) :=
        one_div_le_one_div_of_le (by linarith)
          (by linarith [Real.add_one_le_exp ((step_count : ℝ) * rate)])

/-- **The matching penalty.** Weight decay with
`decay_strength = 1 / (learning_rate * step_count)` leaves the share
`1 / (1 + step_count * (learning_rate * kernel_strength))`. -/
theorem ridge_share_eq
    {learning_rate : ℝ}
    {kernel_strength : ℝ}
    {step_count : ℕ}
    (learning_rate_pos : 0 < learning_rate)
    (step_count_pos : 0 < step_count)
    (kernel_strength_nonneg : 0 ≤ kernel_strength) :
    let decay_strength := 1 / (learning_rate * step_count)  -- the penalty that matches `step_count` steps of early stopping
    let ridge_share    := decay_strength / (kernel_strength + decay_strength)
    let stopped_share  :=
      1 / (1 + step_count * (learning_rate * kernel_strength))
    ridge_share = stopped_share := by
  unfold_named_pieces
  have step_count_real_pos : (0 : ℝ) < step_count := by
    exact_mod_cast step_count_pos
  have decay_denominator_pos : 0 < learning_rate * step_count :=
    mul_pos learning_rate_pos step_count_real_pos
  have sum_pos : 0 < kernel_strength + 1 / (learning_rate * step_count) :=
    add_pos_of_nonneg_of_pos kernel_strength_nonneg
      (one_div_pos.mpr decay_denominator_pos)
  have stopped_denominator_pos :
      0 < 1 + step_count * (learning_rate * kernel_strength) :=
    add_pos_of_pos_of_nonneg one_pos
      (mul_nonneg step_count_real_pos.le
        (mul_nonneg learning_rate_pos.le kernel_strength_nonneg))
  rw [div_eq_div_iff sum_pos.ne' stopped_denominator_pos.ne']
  field_simp
  ring

end Share

/-! ### The fit that weight decay rests at -/

section Fit

open ContinuousLinearMap

variable {Weights Outputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]

/-- The fit that weight decay with penalty `decay_strength` rests at, when the
error at the start lies along a direction of strength `kernel_strength`. -/
noncomputable def GET_RIDGE_FIT
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (start_weights : Weights)
    (kernel_strength : ℝ)
    (decay_strength : ℝ) : Weights :=
  start_weights + (kernel_strength + decay_strength)⁻¹ •
    adjoint predict
      (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels start_weights)

/-- One step of gradient descent with weight decay `decay_strength` towards the
start `start_weights`. -/
noncomputable def TAKE_DECAY_STEP
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (decay_strength : ℝ)
    (start_weights : Weights)
    (weights : Weights) : Weights :=
  TAKE_GRADIENT_STEP predict labels learning_rate weights
    - (learning_rate * decay_strength) • (weights - start_weights)

variable (predict : Weights →L[ℝ] Outputs) (labels : Outputs)
  (start_weights : Weights) {kernel_strength decay_strength : ℝ}

/-- **What weight decay leaves.** The share
`decay_strength / (kernel_strength + decay_strength)` of the error. -/
theorem residual_ridgeFit
    (strengths_sum_ne_zero : kernel_strength + decay_strength ≠ 0)
    (residual_is_stretched :
      predict (adjoint predict
        (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
          start_weights))
        = kernel_strength
          • GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
              start_weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let ridge_fit :=
      GET_RIDGE_FIT predict labels start_weights kernel_strength
        decay_strength
    let ridge_residual :=
      GET_RESIDUAL linear_predict labels ridge_fit
    let start_residual :=
      GET_RESIDUAL linear_predict labels start_weights
    let share_left     :=
      decay_strength / (kernel_strength + decay_strength)  -- the penalty's part of the total pull
    let left_over      := share_left • start_residual
    ridge_residual = left_over := by
  unfold_named_pieces
  -- The fit moves the residual down by its pull, divided by the total.
  have residual_after_fit :
      GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
          (GET_RIDGE_FIT predict labels start_weights kernel_strength
            decay_strength)
        = GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels start_weights
          - (kernel_strength + decay_strength)⁻¹
            • predict (adjoint predict
              (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
                start_weights)) := by
    simp only [GET_RESIDUAL, GET_RIDGE_FIT, ContinuousLinearMap.coe_coe,
      map_add, map_smul]
    abel
  have inverse_cancels :
      (kernel_strength + decay_strength)⁻¹
        * (kernel_strength + decay_strength) = 1 :=
    inv_mul_cancel₀ strengths_sum_ne_zero
  have share_coefficient :
      decay_strength / (kernel_strength + decay_strength)
        = 1 - (kernel_strength + decay_strength)⁻¹ * kernel_strength := by
    rw [div_eq_inv_mul]
    linear_combination inverse_cancels
  rw [residual_after_fit, residual_is_stretched, smul_smul, share_coefficient,
    sub_smul, one_smul]

/-- **The resting point.** At the weight-decay fit, the pull of the data and
the pull of the penalty balance. -/
theorem ridge_stationary
    (strengths_sum_ne_zero : kernel_strength + decay_strength ≠ 0)
    (residual_is_stretched :
      predict (adjoint predict
        (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
          start_weights))
        = kernel_strength
          • GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
              start_weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let ridge_fit :=
      GET_RIDGE_FIT predict labels start_weights kernel_strength
        decay_strength
    let data_pull    :=
      adjoint predict (GET_RESIDUAL linear_predict labels ridge_fit)
    let penalty_pull := decay_strength • (ridge_fit - start_weights)
    data_pull = penalty_pull := by
  unfold_named_pieces
  have ridge_residual :
      GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
          (GET_RIDGE_FIT predict labels start_weights kernel_strength
            decay_strength)
        = (decay_strength / (kernel_strength + decay_strength))
          • GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
              start_weights :=
    residual_ridgeFit predict labels start_weights strengths_sum_ne_zero
      residual_is_stretched
  rw [ridge_residual, map_smul, GET_RIDGE_FIT, add_sub_cancel_left, smul_smul,
    div_eq_mul_inv]

/-- **Gradient descent with weight decay rests there.** -/
theorem decayStep_ridgeFit
    (learning_rate : ℝ)
    (strengths_sum_ne_zero : kernel_strength + decay_strength ≠ 0)
    (residual_is_stretched :
      predict (adjoint predict
        (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
          start_weights))
        = kernel_strength
          • GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
              start_weights) :
    let ridge_fit :=
      GET_RIDGE_FIT predict labels start_weights kernel_strength
        decay_strength
    let stepped_fit :=
      TAKE_DECAY_STEP predict labels learning_rate decay_strength
        start_weights ridge_fit
    stepped_fit = ridge_fit := by
  unfold_named_pieces
  have stationary :
      adjoint predict
          (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
            (GET_RIDGE_FIT predict labels start_weights kernel_strength
              decay_strength))
        = decay_strength
          • (GET_RIDGE_FIT predict labels start_weights kernel_strength
              decay_strength - start_weights) :=
    ridge_stationary predict labels start_weights strengths_sum_ne_zero
      residual_is_stretched
  rw [TAKE_DECAY_STEP, TAKE_GRADIENT_STEP, stationary, smul_smul,
    add_sub_cancel_right]

/-- **Weight decay is spare parameters.** The answer at a new input with
features `features` moves by the overlap divided by
`kernel_strength + decay_strength`. -/
theorem inner_ridgeFit
    (features : Weights)
    (kernel_strength : ℝ)
    (decay_strength : ℝ) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let ridge_fit :=
      GET_RIDGE_FIT predict labels start_weights kernel_strength
        decay_strength
    let answer_at_fit   := inner ℝ features ridge_fit
    let answer_at_start := inner ℝ features start_weights
    let overlap         := inner ℝ (predict features)
      (GET_RESIDUAL linear_predict labels start_weights)
    let shift           := overlap / (kernel_strength + decay_strength)
    answer_at_fit = answer_at_start + shift := by
  unfold_named_pieces
  rw [GET_RIDGE_FIT, inner_add_right, real_inner_smul_right,
    adjoint_inner_right]
  ring

end Fit

end SquigglyLine
