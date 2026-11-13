/-
Chinchilla: how to split a compute budget.

The loss above the floor is

    param_cost / param_count + data_cost / data_count

with `param_count` parameters and `data_count` data. The budget fixes
`param_count * data_count`.

| Name                   | Meaning                                         |
|------------------------|-------------------------------------------------|
| `GET_LOSS_ABOVE_FLOOR` | the two terms of the loss, added                |
| `IS_BALANCED_SPLIT`    | the two terms of the loss are equal             |

* `four_mul_div_le_sq` : for any split, the loss above the floor squared is
  at least `4 * param_cost * data_cost / (param_count * data_count)`.
* `balanced_loss_sq` : a balanced split reaches that bound.
* `balanced_is_optimal` : so no split with the same budget does better.
* `balanced_ratio` : at the best split `param_count / data_count` is
  `param_cost / data_cost`, whatever the budget.
* `balanced_scale` : scaling parameters and data by the same factor keeps the
  split balanced.
* `chinchilla_optimal` : the same with the floor added.
* `balanced_is_optimal_rpow` : the same when both terms fall as a common
  power of their size.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import SquigglyLine.Style

namespace SquigglyLine

/-! ## Helper functions -/

/-- The loss above the floor for one split of the budget. One term falls as
the parameters grow, the other as the data grows.
Python: `param_cost / param_count + data_cost / data_count`. -/
noncomputable abbrev GET_LOSS_ABOVE_FLOOR
    (param_cost data_cost : ℝ)
    (param_count data_count : ℝ) : ℝ :=
  param_cost / param_count + data_cost / data_count

/-- A split is balanced when the two terms of the loss are equal.
Python: `param_cost / param_count == data_cost / data_count`. -/
abbrev IS_BALANCED_SPLIT
    (param_cost data_cost : ℝ)
    (param_count data_count : ℝ) : Prop :=
  param_cost / param_count = data_cost / data_count

/-! ## The theorems -/

/-- **A sum with a fixed product.** For any split of the budget, the loss
above the floor squared is at least `4 * param_cost * data_cost` over the
budget. -/
theorem four_mul_div_le_sq
    (param_cost data_cost : ℝ)
    (param_count data_count : ℝ) :
    let loss_above_floor :=
      GET_LOSS_ABOVE_FLOOR param_cost data_cost param_count data_count
    let budget      := param_count * data_count               -- compute spent: every parameter sees every piece of data
    let lower_bound := 4 * (param_cost * data_cost / budget)  -- the product of the two terms, times 4: (a + b)² ≥ 4ab
    lower_bound ≤ loss_above_floor ^ 2 :=
  -- A sum of two numbers, squared, is at least four times their product.
  calc 4 * (param_cost * data_cost / (param_count * data_count))
      = 4 * (param_cost / param_count) * (data_cost / data_count) := by
        rw [← div_mul_div_comm, mul_assoc]
    _ ≤ (param_cost / param_count + data_cost / data_count) ^ 2 :=
        four_mul_le_sq_add _ _

/-- **What the best split buys.** With the two terms balanced, the loss above
the floor squared is `4 * param_cost * data_cost` over the budget. -/
theorem balanced_loss_sq
    {param_cost data_cost : ℝ}
    {balanced_param_count balanced_data_count : ℝ}
    (split_is_balanced :
      IS_BALANCED_SPLIT param_cost data_cost
        balanced_param_count balanced_data_count) :
    let loss_above_floor :=
      GET_LOSS_ABOVE_FLOOR param_cost data_cost
        balanced_param_count balanced_data_count
    let budget      := balanced_param_count * balanced_data_count
    let lower_bound := 4 * (param_cost * data_cost / budget)  -- the bound of `four_mul_div_le_sq`: (a + b)² = 4ab when a = b
    loss_above_floor ^ 2 = lower_bound := by
  unfold_named_pieces
  unfold GET_LOSS_ABOVE_FLOOR
  unfold IS_BALANCED_SPLIT at split_is_balanced
  rw [← div_mul_div_comm, ← split_is_balanced]
  ring

/-- **The best split balances the two terms.** If a split is balanced, no
other split with the same budget has a smaller loss. -/
theorem balanced_is_optimal
    {param_cost data_cost : ℝ}
    {param_count data_count : ℝ}
    {balanced_param_count balanced_data_count : ℝ}
    (param_cost_nonneg : 0 ≤ param_cost)
    (data_cost_nonneg : 0 ≤ data_cost)
    (balanced_param_count_pos : 0 < balanced_param_count)
    (balanced_data_count_pos : 0 < balanced_data_count)
    (param_count_pos : 0 < param_count)
    (data_count_pos : 0 < data_count)
    (split_is_balanced :
      IS_BALANCED_SPLIT param_cost data_cost
        balanced_param_count balanced_data_count)
    (same_budget :
      balanced_param_count * balanced_data_count = param_count * data_count) :
    let balanced_loss :=
      GET_LOSS_ABOVE_FLOOR param_cost data_cost
        balanced_param_count balanced_data_count
    let other_loss :=
      GET_LOSS_ABOVE_FLOOR param_cost data_cost param_count data_count
    balanced_loss ≤ other_loss := by
  unfold_named_pieces
  unfold GET_LOSS_ABOVE_FLOOR
  have balanced_loss_nonneg :
      0 ≤ param_cost / balanced_param_count
        + data_cost / balanced_data_count :=
    add_nonneg (div_nonneg param_cost_nonneg balanced_param_count_pos.le)
      (div_nonneg data_cost_nonneg balanced_data_count_pos.le)
  have other_loss_nonneg :
      0 ≤ param_cost / param_count + data_cost / data_count :=
    add_nonneg (div_nonneg param_cost_nonneg param_count_pos.le)
      (div_nonneg data_cost_nonneg data_count_pos.le)
  -- Both losses are nonnegative, so it is enough to compare their squares.
  refine (sq_le_sq₀ balanced_loss_nonneg other_loss_nonneg).mp ?_
  -- The balanced split meets the lower bound that every split obeys.
  calc (param_cost / balanced_param_count
          + data_cost / balanced_data_count) ^ 2
      = 4 * (param_cost * data_cost
          / (balanced_param_count * balanced_data_count)) :=
        balanced_loss_sq split_is_balanced
    _ = 4 * (param_cost * data_cost / (param_count * data_count)) := by
        rw [same_budget]
    _ ≤ (param_cost / param_count + data_cost / data_count) ^ 2 :=
        four_mul_div_le_sq param_cost data_cost param_count data_count

/-- **A fixed ratio.** At the best split, parameters over data is
`param_cost / data_cost`, whatever the budget. -/
theorem balanced_ratio
    {param_cost data_cost : ℝ}
    {balanced_param_count balanced_data_count : ℝ}
    (data_cost_ne_zero : data_cost ≠ 0)
    (balanced_param_count_ne_zero : balanced_param_count ≠ 0)
    (balanced_data_count_ne_zero : balanced_data_count ≠ 0)
    (split_is_balanced :
      IS_BALANCED_SPLIT param_cost data_cost
        balanced_param_count balanced_data_count) :
    let params_per_data := balanced_param_count / balanced_data_count
    let cost_ratio      := param_cost / data_cost  -- the budget is not in it: the ratio is the same at every size
    params_per_data = cost_ratio := by
  unfold_named_pieces
  unfold IS_BALANCED_SPLIT at split_is_balanced
  -- Clear the fractions on both sides; what is left is the same equation.
  rw [div_eq_div_iff balanced_param_count_ne_zero
    balanced_data_count_ne_zero] at split_is_balanced
  rw [div_eq_div_iff balanced_data_count_ne_zero data_cost_ne_zero]
  linarith

/-- **They grow together.** Scaling parameters and data by the same factor
keeps the split balanced. -/
theorem balanced_scale
    {param_cost data_cost : ℝ}
    {balanced_param_count balanced_data_count : ℝ}
    (scale : ℝ)
    (split_is_balanced :
      IS_BALANCED_SPLIT param_cost data_cost
        balanced_param_count balanced_data_count) :
    let scaled_param_count := scale * balanced_param_count
    let scaled_data_count  := scale * balanced_data_count  -- the same factor on both: each term is divided by it
    IS_BALANCED_SPLIT param_cost data_cost
      scaled_param_count scaled_data_count := by
  unfold_named_pieces
  unfold IS_BALANCED_SPLIT at split_is_balanced ⊢
  rw [mul_comm scale balanced_param_count,
    mul_comm scale balanced_data_count, ← div_div, ← div_div,
    split_is_balanced]

/-- **With the floor.** The whole loss, floor included, is smallest at the
balanced split. -/
theorem chinchilla_optimal
    {param_cost data_cost : ℝ}
    {param_count data_count : ℝ}
    {balanced_param_count balanced_data_count : ℝ}
    (loss_floor : ℝ)
    (param_cost_nonneg : 0 ≤ param_cost)
    (data_cost_nonneg : 0 ≤ data_cost)
    (balanced_param_count_pos : 0 < balanced_param_count)
    (balanced_data_count_pos : 0 < balanced_data_count)
    (param_count_pos : 0 < param_count)
    (data_count_pos : 0 < data_count)
    (split_is_balanced :
      IS_BALANCED_SPLIT param_cost data_cost
        balanced_param_count balanced_data_count)
    (same_budget :
      balanced_param_count * balanced_data_count = param_count * data_count) :
    let balanced_param_term := param_cost / balanced_param_count
    let balanced_data_term  := data_cost / balanced_data_count
    let param_term          := param_cost / param_count
    let data_term           := data_cost / data_count
    let balanced_loss :=
      loss_floor + balanced_param_term + balanced_data_term  -- the floor is what no amount of compute removes
    let other_loss := loss_floor + param_term + data_term
    balanced_loss ≤ other_loss := by
  unfold_named_pieces
  -- The floor is the same on both sides, so only the part above it matters.
  have balanced_is_best :
      param_cost / balanced_param_count + data_cost / balanced_data_count
        ≤ param_cost / param_count + data_cost / data_count :=
    balanced_is_optimal param_cost_nonneg data_cost_nonneg
      balanced_param_count_pos balanced_data_count_pos param_count_pos
      data_count_pos split_is_balanced same_budget
  linarith [balanced_is_best]

/-- **Any common power.** The same holds when both terms fall as the same
power `exponent` of their size. -/
theorem balanced_is_optimal_rpow
    {param_cost data_cost : ℝ}
    {param_count data_count : ℝ}
    {balanced_param_count balanced_data_count : ℝ}
    (exponent : ℝ)
    (param_cost_nonneg : 0 ≤ param_cost)
    (data_cost_nonneg : 0 ≤ data_cost)
    (balanced_param_count_pos : 0 < balanced_param_count)
    (balanced_data_count_pos : 0 < balanced_data_count)
    (param_count_pos : 0 < param_count)
    (data_count_pos : 0 < data_count)
    (split_is_balanced :
      IS_BALANCED_SPLIT param_cost data_cost
        (balanced_param_count ^ exponent) (balanced_data_count ^ exponent))
    (same_budget :
      balanced_param_count * balanced_data_count = param_count * data_count) :
    let balanced_loss :=
      GET_LOSS_ABOVE_FLOOR param_cost data_cost
        (balanced_param_count ^ exponent) (balanced_data_count ^ exponent)  -- each size enters through its power
    let other_loss :=
      GET_LOSS_ABOVE_FLOOR param_cost data_cost
        (param_count ^ exponent) (data_count ^ exponent)
    balanced_loss ≤ other_loss :=
  -- The powers are sizes too: positive, and with the same product on both
  -- sides, because a power of a product is the product of the powers.
  balanced_is_optimal param_cost_nonneg data_cost_nonneg
    (Real.rpow_pos_of_pos balanced_param_count_pos exponent)
    (Real.rpow_pos_of_pos balanced_data_count_pos exponent)
    (Real.rpow_pos_of_pos param_count_pos exponent)
    (Real.rpow_pos_of_pos data_count_pos exponent) split_is_balanced
    (by rw [← Real.mul_rpow balanced_param_count_pos.le
          balanced_data_count_pos.le,
        ← Real.mul_rpow param_count_pos.le data_count_pos.le, same_budget])

end SquigglyLine
