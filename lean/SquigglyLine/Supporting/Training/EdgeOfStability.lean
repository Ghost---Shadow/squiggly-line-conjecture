/-
The edge of stability.

Follow a direction `direction` of the labels that the kernel stretches by
`kernel_strength`. With step size `learning_rate`, each gradient step
multiplies the size of the error along `direction` by
`|1 - learning_rate * kernel_strength|`
(`abs_inner_residual_iterate_gradientStep`).

* `shrinks_below_edge` : if `0 < learning_rate * kernel_strength < 2` the error
  never grows, and the factor is below one (`abs_one_sub_lt_one_iff`).
* `holds_at_edge` : if `learning_rate * kernel_strength = 2` the error keeps
  its size for ever.
* `grows_past_edge` : if `learning_rate * kernel_strength ≥ 2` the error after
  `step_count` steps is at least
  `1 + step_count * (learning_rate * kernel_strength - 2)` times what it was.
* `stable_iff_lt_two_div` : a direction is stable exactly when the step size
  is below `2 / kernel_strength`.

Also here: `one_add_mul_le_abs_pow`, the growth of the factor's powers past the
edge.
-/
import SquigglyLine.Supporting.Training.SpectralBias

namespace SquigglyLine

/-! ### The factor `|1 - rate|` -/

section Factor

/-- **The edge is at two.** The factor is below one exactly when
`0 < rate < 2`. -/
theorem abs_one_sub_lt_one_iff
    {rate : ℝ} :
    let factor_is_below_one := |1 - rate| < 1
    let rate_is_positive    := 0 < rate
    let rate_is_below_edge  := rate < 2  -- `1 - rate` must stay above `-1`
    let rate_in_range       := rate_is_positive ∧ rate_is_below_edge
    factor_is_below_one ↔ rate_in_range := by
  unfold_named_pieces
  rw [abs_lt]
  constructor
  · rintro ⟨above_minus_one, below_one⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨positive, below_two⟩
    exact ⟨by linarith, by linarith⟩

/-- **Stable exactly below `2 / kernel_strength`.** -/
theorem stable_iff_lt_two_div
    {learning_rate : ℝ}
    {kernel_strength : ℝ}
    (learning_rate_pos : 0 < learning_rate)
    (kernel_strength_pos : 0 < kernel_strength) :
    let factor_is_below_one := |1 - learning_rate * kernel_strength| < 1
    let step_is_below_edge  := learning_rate < 2 / kernel_strength  -- `rate < 2`, divided by `kernel_strength`
    factor_is_below_one ↔ step_is_below_edge := by
  unfold_named_pieces
  rw [propext (abs_one_sub_lt_one_iff
    (rate := learning_rate * kernel_strength)),
    lt_div_iff₀ kernel_strength_pos]
  exact ⟨fun in_range => in_range.2,
    fun below_edge => ⟨mul_pos learning_rate_pos kernel_strength_pos,
      below_edge⟩⟩

/-- Past the edge the factor's powers grow at least linearly. -/
theorem one_add_mul_le_abs_pow
    {rate : ℝ}
    (rate_past_edge : 2 ≤ rate)
    (step_count : ℕ) :
    let linear_growth := 1 + step_count * (rate - 2)
    let true_growth   := |1 - rate| ^ step_count
    linear_growth ≤ true_growth := by
  unfold_named_pieces
  -- Past the edge `|1 - rate|` is `1 + (rate - 2)`; Bernoulli does the rest.
  have factor_eq : |1 - rate| = 1 + (rate - 2) := by
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [factor_eq]
  exact one_add_mul_le_pow (by linarith) step_count

end Factor

/-! ### One direction of the kernel -/

section Direction

open ContinuousLinearMap

variable {Weights Outputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]

/-- After `step_count` steps the size of the error along `direction` is
`|1 - learning_rate * kernel_strength| ^ step_count` times what it was. -/
theorem abs_inner_residual_iterate_gradientStep
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
    let start_size   := |inner ℝ direction
      (GET_RESIDUAL linear_predict labels start_weights)|
    let trained_size := |inner ℝ direction
      (GET_RESIDUAL linear_predict labels trained_weights)|
    let factor       := |1 - learning_rate * kernel_strength|  -- the size of one step's multiplier
    trained_size = factor ^ step_count * start_size := by
  unfold_named_pieces
  rw [inner_residual_iterate_gradientStep predict labels learning_rate
    start_weights direction_is_stretched step_count, abs_mul, abs_pow]

/-- **Below the edge the error never grows.** -/
theorem shrinks_below_edge
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    {learning_rate : ℝ}
    {kernel_strength : ℝ}
    (rate_is_positive : 0 < learning_rate * kernel_strength)
    (rate_below_edge : learning_rate * kernel_strength < 2)
    (start_weights : Weights)
    {direction : Outputs}
    (direction_is_stretched :
      predict (adjoint predict direction) = kernel_strength • direction)
    (step_count : ℕ) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights
    let start_size   := |inner ℝ direction
      (GET_RESIDUAL linear_predict labels start_weights)|
    let trained_size := |inner ℝ direction
      (GET_RESIDUAL linear_predict labels trained_weights)|
    trained_size ≤ start_size := by
  unfold_named_pieces
  have size_formula :
      |inner ℝ direction
          (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
            ((TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
              start_weights))|
        = |1 - learning_rate * kernel_strength| ^ step_count
          * |inner ℝ direction
            (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
              start_weights)| :=
    abs_inner_residual_iterate_gradientStep predict labels learning_rate
      start_weights direction_is_stretched step_count
  rw [size_formula]
  have factor_le_one : |1 - learning_rate * kernel_strength| ≤ 1 :=
    (abs_one_sub_lt_one_iff.mpr
      ⟨rate_is_positive, rate_below_edge⟩).le
  exact mul_le_of_le_one_left (abs_nonneg _)
    (pow_le_one₀ (abs_nonneg _) factor_le_one)

/-- **On the edge the error keeps its size.** It flips sign at each step and
never dies down. -/
theorem holds_at_edge
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    {learning_rate : ℝ}
    {kernel_strength : ℝ}
    (rate_at_edge : learning_rate * kernel_strength = 2)
    (start_weights : Weights)
    {direction : Outputs}
    (direction_is_stretched :
      predict (adjoint predict direction) = kernel_strength • direction)
    (step_count : ℕ) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights
    let start_size   := |inner ℝ direction
      (GET_RESIDUAL linear_predict labels start_weights)|
    let trained_size := |inner ℝ direction
      (GET_RESIDUAL linear_predict labels trained_weights)|
    trained_size = start_size := by
  unfold_named_pieces
  have size_formula :
      |inner ℝ direction
          (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
            ((TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
              start_weights))|
        = |1 - learning_rate * kernel_strength| ^ step_count
          * |inner ℝ direction
            (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
              start_weights)| :=
    abs_inner_residual_iterate_gradientStep predict labels learning_rate
      start_weights direction_is_stretched step_count
  -- At the edge the factor is `|1 - 2| = 1`.
  rw [size_formula, rate_at_edge]
  norm_num

/-- **Past the edge the error grows without limit.** After `step_count` steps
it is at least `1 + step_count * (learning_rate * kernel_strength - 2)` times
what it was. -/
theorem grows_past_edge
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    {learning_rate : ℝ}
    {kernel_strength : ℝ}
    (rate_past_edge : 2 ≤ learning_rate * kernel_strength)
    (start_weights : Weights)
    {direction : Outputs}
    (direction_is_stretched :
      predict (adjoint predict direction) = kernel_strength • direction)
    (step_count : ℕ) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights
    let start_size   := |inner ℝ direction
      (GET_RESIDUAL linear_predict labels start_weights)|
    let trained_size := |inner ℝ direction
      (GET_RESIDUAL linear_predict labels trained_weights)|
    let rate         := learning_rate * kernel_strength
    let growth       := 1 + step_count * (rate - 2)  -- `rate - 2` is how far past the edge
    growth * start_size ≤ trained_size := by
  unfold_named_pieces
  have size_formula :
      |inner ℝ direction
          (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
            ((TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
              start_weights))|
        = |1 - learning_rate * kernel_strength| ^ step_count
          * |inner ℝ direction
            (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
              start_weights)| :=
    abs_inner_residual_iterate_gradientStep predict labels learning_rate
      start_weights direction_is_stretched step_count
  have growth_le_power :
      1 + step_count * (learning_rate * kernel_strength - 2)
        ≤ |1 - learning_rate * kernel_strength| ^ step_count :=
    one_add_mul_le_abs_pow rate_past_edge step_count
  rw [size_formula]
  exact mul_le_mul_of_nonneg_right growth_le_power (abs_nonneg _)

end Direction

end SquigglyLine
