/-
A network for which the conjecture is true.

Stack `L` of the two-neuron folds of `Depth.lean`. The curve this network
draws passes within `1 / 2 ^ L` of every point of the unit square. Each layer
halves the distance.

So for this family "more layers, squigglier, closer" holds, with an
exponential rate. The weights are chosen, not random.
-/
import SquigglyLine.Networks.Bridge
import SquigglyLine.Theorem.Oscillation

namespace SquigglyLine

/-- **Each fold halves the distance.** For any input and any label in the unit interval,
the `L`-fold network takes that label at some input within `1 / 2 ^ L`. -/
theorem iterate_tent_covers (L : ℕ) {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ∃ x' ∈ Set.Icc (0 : ℝ) 1, |x - x'| ≤ 1 / 2 ^ L ∧ APPLY_TENT^[L] x' = y := by
  induction L generalizing x with
  | zero =>
    refine ⟨y, hy, ?_, rfl⟩
    rw [pow_zero, div_one, abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  | succ L ih =>
    obtain ⟨z, hz, hclose, hfit⟩ := ih (tent_mem_Icc hx.1 hx.2)
    have hstep : (1 : ℝ) / 2 ^ (L + 1) = 1 / 2 ^ L / 2 := by rw [pow_succ]; field_simp
    rcases le_total x (1 / 2) with hhalf | hhalf
    · refine ⟨z / 2, ⟨by linarith [hz.1], by linarith [hz.2]⟩, ?_, ?_⟩
      · rw [tent_of_le_half hx.1 hhalf] at hclose
        rw [hstep, show x - z / 2 = (2 * x - z) / 2 by ring, abs_div, abs_two]
        exact div_le_div_of_nonneg_right hclose (by norm_num)
      · rw [Function.iterate_succ_apply,
          tent_of_le_half (by linarith [hz.1]) (by linarith [hz.2]),
          show 2 * (z / 2) = z by ring, hfit]
    · refine ⟨1 - z / 2, ⟨by linarith [hz.2], by linarith [hz.1]⟩, ?_, ?_⟩
      · rw [tent_of_half_le hhalf] at hclose
        rw [hstep, show x - (1 - z / 2) = -((2 - 2 * x - z) / 2) by ring, abs_neg, abs_div,
          abs_two]
        exact div_le_div_of_nonneg_right hclose (by norm_num)
      · rw [Function.iterate_succ_apply, tent_of_half_le (by linarith [hz.2]),
          show 2 - 2 * (1 - z / 2) = z by ring, hfit]

/-- **More layers, closer.** The curve drawn by `L` two-neuron layers passes within
`1 / 2 ^ L` of every point of the unit square. -/
theorem nearestDist_iterate_tent_le (L : ℕ) (p : DataPoint ℝ) (hx : p.1 ∈ Set.Icc (0 : ℝ) 1)
    (hy : p.2 ∈ Set.Icc (0 : ℝ) 1) : GET_NEAREST_DISTANCE (APPLY_TENT^[L]) p ≤ 1 / 2 ^ L := by
  obtain ⟨x', -, hclose, hfit⟩ := iterate_tent_covers L hx hy
  calc GET_NEAREST_DISTANCE (APPLY_TENT^[L]) p
      ≤ dist (EMBED_DATA_POINT p) (EMBED_DATA_POINT (x', APPLY_TENT^[L] x')) :=
        Metric.infDist_le_dist_of_mem (footpoint_mem_curve _ (x', APPLY_TENT^[L] x'))
    _ = |p.1 - x'| := by simp [dist_embed, hfit, Real.dist_eq, Real.sqrt_sq_eq_abs]
    _ ≤ 1 / 2 ^ L := hclose

end SquigglyLine
