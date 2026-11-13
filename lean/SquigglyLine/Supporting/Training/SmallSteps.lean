/-
Many small steps.

Cover a distance `distance` in `step_count` equal steps.

* `quadratic_cost_total` : if a step of size `step_size` costs
  `cost_rate * step_size²`, the steps cost `cost_rate * distance² / step_count`
  in all. More steps, less cost.
* `linear_cost_total` : if a step of size `step_size` costs
  `cost_rate * step_size`, the steps cost `cost_rate * distance` in all. More
  steps gain nothing.
* `small_steps_keep` : if a step of size `step_size` keeps at least
  `1 - cost_rate * step_size²`, the `step_count` steps together keep at least
  `1 - cost_rate * distance² / step_count`.
* `turn_in_steps_keeps` : polarizers. Turning light through any angle `angle`
  in `plate_count` plates keeps at least `1 - angle² / (2 * plate_count)` of
  its length.
* `cos_pow_le_cos_half_pow` : replacing every plate by two of half the turn
  never loses.

Also here: `cos_le_cos_half_sq` (one plate keeps no more than two plates of
half the turn).
-/
import SquigglyLine.Supporting.Training.LeastAction
import SquigglyLine.Supporting.Training.SpectralBias
import SquigglyLine.Networks.ThreePolarizers

namespace SquigglyLine

/-! ### Counting the cost -/

section Counting

variable {step_count : ℕ}

/-- **A square-law cost shrinks with the number of steps.** -/
theorem quadratic_cost_total
    (step_count_pos : 0 < step_count)
    (cost_rate : ℝ)
    (distance : ℝ) :
    let step_size  := distance / step_count
    let step_cost  := cost_rate * step_size ^ 2  -- a square-law cost
    let total_cost := step_count * step_cost
    let formula    := cost_rate * distance ^ 2 / step_count
    total_cost = formula := by
  unfold_named_pieces
  have step_count_ne_zero : (step_count : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr step_count_pos.ne'
  field_simp

/-- **A cost in proportion to the step does not.** -/
theorem linear_cost_total
    (step_count_pos : 0 < step_count)
    (cost_rate : ℝ)
    (distance : ℝ) :
    let step_size  := distance / step_count
    let step_cost  := cost_rate * step_size
    let total_cost := step_count * step_cost
    let formula    := cost_rate * distance
    total_cost = formula := by
  unfold_named_pieces
  have step_count_ne_zero : (step_count : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr step_count_pos.ne'
  field_simp

/-- **Many small steps.** Suppose a step of size `step_size` keeps at least
`1 - cost_rate * step_size²` of what there is. Then `step_count` steps of size
`distance / step_count` keep at least
`1 - cost_rate * distance² / step_count`. -/
theorem small_steps_keep
    (step_count_pos : 0 < step_count)
    {cost_rate : ℝ}
    {distance : ℝ}
    {keep : RealFunction}
    (step_keeps : ∀ step_size,
      1 - cost_rate * step_size ^ 2 ≤ keep step_size)
    (step_is_small : cost_rate * (distance / step_count) ^ 2 ≤ 1) :
    let step_size  := distance / step_count
    let guaranteed := 1 - cost_rate * distance ^ 2 / step_count
    let kept       := keep step_size ^ step_count
    guaranteed ≤ kept := by
  unfold_named_pieces
  have total_cost :
      (step_count : ℝ) * (cost_rate * (distance / step_count) ^ 2)
        = cost_rate * distance ^ 2 / step_count :=
    quadratic_cost_total step_count_pos cost_rate distance
  -- Bernoulli: `step_count` steps of cost `step_cost` keep `1 - total cost`.
  calc 1 - cost_rate * distance ^ 2 / step_count
      = 1 - step_count * (cost_rate * (distance / step_count) ^ 2) := by
        rw [total_cost]
    _ ≤ (1 - cost_rate * (distance / step_count) ^ 2) ^ step_count :=
        one_sub_mul_le_pow_one_sub step_is_small step_count
    _ ≤ keep (distance / step_count) ^ step_count :=
        pow_le_pow_left₀ (by linarith) (step_keeps _) step_count

end Counting

/-! ### The polarizers -/

section Plates

open Real

/-- **Any turn, in enough plates.** Turning light through an angle `angle` in
`plate_count` equal plates keeps at least `1 - angle² / (2 * plate_count)` of
its length. -/
theorem turn_in_steps_keeps
    {plate_count : ℕ}
    (plate_count_pos : 0 < plate_count)
    {angle : ℝ}
    (turn_is_small : (angle / plate_count) ^ 2 ≤ 2) :
    let plate_turn := angle / plate_count
    let guaranteed := 1 - angle ^ 2 / (2 * plate_count)  -- `cost_rate = 1 / 2`: `cos x ≥ 1 - x² / 2`
    let kept       := cos plate_turn ^ plate_count
    guaranteed ≤ kept := by
  unfold_named_pieces
  have small_steps := small_steps_keep plate_count_pos (cost_rate := 1 / 2)
    (distance := angle) (keep := cos)
    (fun step_size => by linarith [one_sub_sq_div_two_le_cos (x := step_size)])
    (by linarith)
  calc 1 - angle ^ 2 / (2 * plate_count)
      = 1 - 1 / 2 * angle ^ 2 / plate_count := by ring
    _ ≤ cos (angle / plate_count) ^ plate_count := small_steps

/-- One plate keeps no more than two plates of half the turn. -/
theorem cos_le_cos_half_sq
    (turn : ℝ) :
    let kept_by_one_plate  := cos turn
    let kept_by_two_plates := cos (turn / 2) ^ 2
    kept_by_one_plate ≤ kept_by_two_plates := by
  unfold_named_pieces
  -- Two turns, one of `turn` and one of `0`, keep no more than two halves.
  simpa using cos_mul_cos_le_cos_half_sq turn 0

/-- **More plates never hurt.** Replacing each of `plate_count` plates by two of
half the turn keeps at least as much. -/
theorem cos_pow_le_cos_half_pow
    {turn : ℝ}
    (cos_turn_nonneg : 0 ≤ cos turn)
    (plate_count : ℕ) :
    let kept_by_plates := cos turn ^ plate_count
    let kept_by_halves := cos (turn / 2) ^ (2 * plate_count)  -- two plates of half the turn for each plate
    kept_by_plates ≤ kept_by_halves := by
  unfold_named_pieces
  rw [pow_mul]
  exact pow_le_pow_left₀ cos_turn_nonneg (cos_le_cos_half_sq turn) plate_count

end Plates

end SquigglyLine
