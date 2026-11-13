/-
Spectral bias: strong directions are learned first.

Take a direction `direction` of the labels that the kernel only stretches, by
`kernel_strength`.

* `inner_residual_gradientStep` : one gradient step multiplies the error along
  `direction` by `1 - learning_rate * kernel_strength`.
* `inner_residual_iterate_gradientStep` : after `step_count` steps the factor
  is `(1 - learning_rate * kernel_strength) ^ step_count`. Each direction
  shrinks on its own clock.
* `strong_directions_first` : a stronger direction has a smaller share left.
* `spectral_bias` : the share left after `step_count` steps lies between
  `1 - step_count * rate` and `exp (-(step_count * rate))`, where
  `rate = learning_rate * kernel_strength`. The clock of a direction is
  `1 / rate` steps: it cannot be hurried, and it does run out.
* `inner_residual_iterate_of_kernel_eq_zero` : a direction of strength zero is
  never learned.

Also here: `pow_one_sub_anti`, `one_sub_mul_le_pow_one_sub` and
`pow_one_sub_le_exp`, the three facts about `(1 - rate) ^ step_count` that
these rest on.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import SquigglyLine.Networks.DoubleDescent

namespace SquigglyLine

/-! ### The share of an error left after `step_count` steps -/

section Share

/-- A larger rate leaves a smaller share. -/
theorem pow_one_sub_anti
    {small_rate : ℝ}
    {large_rate : ℝ}
    (small_le_large : small_rate ≤ large_rate)
    (large_rate_le_one : large_rate ≤ 1)
    (step_count : ℕ) :
    let large_share := (1 - large_rate) ^ step_count
    let small_share := (1 - small_rate) ^ step_count
    large_share ≤ small_share := by
  unfold_named_pieces
  exact pow_le_pow_left₀ (by linarith) (by linarith) step_count

/-- **It cannot be hurried.** After `step_count` steps at rate `rate`, at
least `1 - step_count * rate` is left. -/
theorem one_sub_mul_le_pow_one_sub
    {rate : ℝ}
    (rate_le_one : rate ≤ 1)
    (step_count : ℕ) :
    let linear_share := 1 - step_count * rate
    let true_share   := (1 - rate) ^ step_count
    linear_share ≤ true_share := by
  unfold_named_pieces
  -- Bernoulli's inequality for the number `-rate`.
  have bernoulli := one_add_mul_le_pow
    (show (-2 : ℝ) ≤ -rate by linarith) step_count  -- Bernoulli needs `-2 ≤ -rate`, true as `rate ≤ 1`
  calc 1 - step_count * rate = 1 + step_count * -rate := by ring
    _ ≤ (1 + -rate) ^ step_count := bernoulli
    _ = (1 - rate) ^ step_count := by rw [← sub_eq_add_neg]

/-- **It does run out.** After `step_count` steps at rate `rate`, at most
`exp (-(step_count * rate))` is left. -/
theorem pow_one_sub_le_exp
    {rate : ℝ}
    (rate_le_one : rate ≤ 1)
    (step_count : ℕ) :
    let true_share := (1 - rate) ^ step_count
    let exp_share  := Real.exp (-(step_count * rate))  -- from `1 - x ≤ exp (-x)`, raised to the power `step_count`
    true_share ≤ exp_share := by
  unfold_named_pieces
  calc (1 - rate) ^ step_count ≤ Real.exp (-rate) ^ step_count :=
        pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg rate)
          step_count
    _ = Real.exp (-(step_count * rate)) := by
        rw [← Real.exp_nat_mul, mul_neg]

/-- **Strong directions are learned first.** With step size `learning_rate`,
a direction of strength `strong_strength` has a smaller share of its error left
than a weaker direction of strength `weak_strength`. -/
theorem strong_directions_first
    {learning_rate : ℝ}
    {weak_strength : ℝ}
    {strong_strength : ℝ}
    (learning_rate_nonneg : 0 ≤ learning_rate)
    (weak_le_strong : weak_strength ≤ strong_strength)
    (strong_rate_le_one : learning_rate * strong_strength ≤ 1)
    (step_count : ℕ) :
    let strong_rate  := learning_rate * strong_strength
    let weak_rate    := learning_rate * weak_strength
    let strong_share := (1 - strong_rate) ^ step_count
    let weak_share   := (1 - weak_rate) ^ step_count
    strong_share ≤ weak_share := by
  unfold_named_pieces
  exact pow_one_sub_anti
    (mul_le_mul_of_nonneg_left weak_le_strong learning_rate_nonneg)
    strong_rate_le_one step_count

end Share

/-! ### One direction of the kernel at a time -/

section Direction

open ContinuousLinearMap

variable {Weights Outputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]

/-- **One step, one direction.** If the kernel stretches `direction` by
`kernel_strength`, a gradient step multiplies the error along `direction` by
`1 - learning_rate * kernel_strength`. -/
theorem inner_residual_gradientStep
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (weights : Weights)
    {direction : Outputs}
    {kernel_strength : ℝ}
    (direction_is_stretched :
      predict (adjoint predict direction) = kernel_strength • direction) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let next_weights :=
      TAKE_GRADIENT_STEP predict labels learning_rate weights
    let error_before := inner ℝ direction
      (GET_RESIDUAL linear_predict labels weights)
    let error_after  := inner ℝ direction
      (GET_RESIDUAL linear_predict labels next_weights)
    let shrink       := 1 - learning_rate * kernel_strength  -- the step removes `learning_rate * kernel_strength` of the error
    error_after = shrink * error_before := by
  unfold_named_pieces
  rw [residual_gradientStep, inner_sub_right, real_inner_smul_right,
    ← kernel_inner_comm, direction_is_stretched, real_inner_smul_left]
  ring

/-- **Each direction on its own clock.** After `step_count` steps the error
along `direction` is `(1 - learning_rate * kernel_strength) ^ step_count`
times what it was at the start. -/
theorem inner_residual_iterate_gradientStep
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (start_weights : Weights)
    {direction : Outputs}
    {kernel_strength : ℝ}
    (direction_is_stretched :
      predict (adjoint predict direction) = kernel_strength • direction)
    (step_count : ℕ) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights
    let start_error   := inner ℝ direction
      (GET_RESIDUAL linear_predict labels start_weights)
    let trained_error := inner ℝ direction
      (GET_RESIDUAL linear_predict labels trained_weights)
    let share_left    :=
      (1 - learning_rate * kernel_strength) ^ step_count  -- one factor per step
    trained_error = share_left * start_error := by
  unfold_named_pieces
  induction step_count with
  | zero => simp
  | succ previous_count earlier_case =>
    -- One more step multiplies the error by one more factor.
    rw [Function.iterate_succ_apply',
      inner_residual_gradientStep predict labels learning_rate _
        direction_is_stretched,
      earlier_case, pow_succ]
    ring

/-- **Strength zero: never learned.** If the kernel sends `direction` to zero,
the error along `direction` stays where it started, however long training
runs. -/
theorem inner_residual_iterate_of_kernel_eq_zero
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (start_weights : Weights)
    {direction : Outputs}
    (kernel_kills_direction : predict (adjoint predict direction) = 0)
    (step_count : ℕ) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights
    let start_error   := inner ℝ direction
      (GET_RESIDUAL linear_predict labels start_weights)
    let trained_error := inner ℝ direction
      (GET_RESIDUAL linear_predict labels trained_weights)
    trained_error = start_error := by
  unfold_named_pieces
  have direction_has_strength_zero :
      predict (adjoint predict direction) = (0 : ℝ) • direction := by
    rw [kernel_kills_direction, zero_smul]
  rw [inner_residual_iterate_gradientStep predict labels learning_rate
    start_weights direction_has_strength_zero step_count]
  simp

/-- **Spectral bias.** If the kernel stretches `direction` by
`kernel_strength` and `learning_rate * kernel_strength ≤ 1`, then after
`step_count` steps the error along `direction` is at least
`1 - step_count * rate` and at most `exp (-(step_count * rate))` of what it
was, where `rate = learning_rate * kernel_strength`. The clock of the
direction is `1 / rate` steps. -/
theorem spectral_bias
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    {learning_rate : ℝ}
    {kernel_strength : ℝ}
    (rate_le_one : learning_rate * kernel_strength ≤ 1)
    (start_weights : Weights)
    {direction : Outputs}
    (direction_is_stretched :
      predict (adjoint predict direction) = kernel_strength • direction)
    (step_count : ℕ) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights
    let start_error   := inner ℝ direction
      (GET_RESIDUAL linear_predict labels start_weights)
    let trained_error := inner ℝ direction
      (GET_RESIDUAL linear_predict labels trained_weights)
    let rate          := learning_rate * kernel_strength
    let lower_bound   := (1 - step_count * rate) * |start_error|
    let upper_bound   := Real.exp (-(step_count * rate)) * |start_error|
    let not_hurried   := lower_bound ≤ |trained_error|
    let runs_out      := |trained_error| ≤ upper_bound
    not_hurried ∧ runs_out := by
  unfold_named_pieces
  have share_nonneg :
      0 ≤ (1 - learning_rate * kernel_strength) ^ step_count :=
    pow_nonneg (by linarith) step_count
  rw [inner_residual_iterate_gradientStep predict labels learning_rate
    start_weights direction_is_stretched step_count, abs_mul,
    abs_of_nonneg share_nonneg]
  exact ⟨mul_le_mul_of_nonneg_right
      (one_sub_mul_le_pow_one_sub rate_le_one step_count) (abs_nonneg _),
    mul_le_mul_of_nonneg_right
      (pow_one_sub_le_exp rate_le_one step_count) (abs_nonneg _)⟩

end Direction

end SquigglyLine
