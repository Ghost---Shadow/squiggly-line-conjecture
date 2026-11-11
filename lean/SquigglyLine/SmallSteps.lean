/-
Many small steps.

Cover a distance `D` in `N` equal steps.

* `quadratic_cost_total` : if a step of size `s` costs `c * s²`, the steps
  cost `c * D² / N` in all. More steps, less cost.
* `linear_cost_total` : if a step of size `s` costs `c * s`, the steps cost
  `c * D` in all. More steps gain nothing.
* `small_steps_keep` : if a step of size `s` keeps at least `1 - c * s²`, the
  `N` steps together keep at least `1 - c * D² / N`.
* `turn_in_steps_keeps` : polarizers. Turning light through any angle `φ` in
  `N` plates keeps at least `1 - φ² / (2N)` of its length.
* `cos_pow_le_cos_half_pow` : replacing every plate by two of half the turn
  never loses.
-/
import SquigglyLine.LeastAction
import SquigglyLine.SpectralBias
import SquigglyLine.ThreePolarizers

namespace SquigglyLine

/-! ### Counting the cost -/

section Counting

variable {N : ℕ}

/-- **A square-law cost shrinks with the number of steps.** -/
theorem quadratic_cost_total (hN : 0 < N) (c D : ℝ) :
    (N : ℝ) * (c * (D / N) ^ 2) = c * D ^ 2 / N := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp

/-- **A cost in proportion to the step does not.** -/
theorem linear_cost_total (hN : 0 < N) (c D : ℝ) : (N : ℝ) * (c * (D / N)) = c * D := by
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  field_simp

/-- **Many small steps.** Suppose a step of size `s` keeps at least `1 - c * s²` of what
there is. Then `N` steps of size `D / N` keep at least `1 - c * D² / N`. -/
theorem small_steps_keep (hN : 0 < N) {c D : ℝ} {keep : ℝ → ℝ}
    (hkeep : ∀ s, 1 - c * s ^ 2 ≤ keep s) (hsmall : c * (D / N) ^ 2 ≤ 1) :
    1 - c * D ^ 2 / N ≤ keep (D / N) ^ N :=
  calc 1 - c * D ^ 2 / N
      = 1 - N * (c * (D / N) ^ 2) := by rw [quadratic_cost_total hN]
    _ ≤ (1 - c * (D / N) ^ 2) ^ N := one_sub_mul_le_pow_one_sub hsmall N
    _ ≤ keep (D / N) ^ N := pow_le_pow_left₀ (by linarith) (hkeep _) N

end Counting

/-! ### The polarizers -/

section Plates

open Real

/-- **Any turn, in enough plates.** Turning light through an angle `φ` in `N` equal plates
keeps at least `1 - φ² / (2N)` of its length. -/
theorem turn_in_steps_keeps {N : ℕ} (hN : 0 < N) {φ : ℝ} (hsmall : (φ / N) ^ 2 ≤ 2) :
    1 - φ ^ 2 / (2 * N) ≤ cos (φ / N) ^ N := by
  have h := small_steps_keep hN (c := 1 / 2) (D := φ) (keep := cos)
    (fun s => by linarith [one_sub_sq_div_two_le_cos (x := s)]) (by linarith)
  calc 1 - φ ^ 2 / (2 * N) = 1 - 1 / 2 * φ ^ 2 / N := by ring
    _ ≤ cos (φ / N) ^ N := h

/-- One plate keeps no more than two plates of half the turn. -/
theorem cos_le_cos_half_sq (a : ℝ) : cos a ≤ cos (a / 2) ^ 2 := by
  simpa using cos_mul_cos_le_cos_half_sq a 0

/-- **More plates never hurt.** Replacing each of `N` plates by two of half the turn keeps
at least as much. -/
theorem cos_pow_le_cos_half_pow {a : ℝ} (ha : 0 ≤ cos a) (N : ℕ) :
    cos a ^ N ≤ cos (a / 2) ^ (2 * N) := by
  rw [pow_mul]
  exact pow_le_pow_left₀ ha (cos_le_cos_half_sq a) N

end Plates

end SquigglyLine
