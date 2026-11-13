/-
Depth multiplies the turns.

`APPLY_TENT` is one layer with two neurons. It folds the interval `[0, 1]` in half:
up from 0 to 1, then down from 1 to 0.

Stack `L` of these layers. On the grid of `2 ^ L + 1` evenly spaced inputs the
output alternates 0, 1, 0, 1, … : zero at the even grid points and one at the
odd ones. So `2L` neurons draw `2 ^ L` straight pieces and turn `2 ^ L - 1`
times. Each layer folds everything the earlier layers made.

This is the precise form of "deeper allows more squiggliness". With one neuron
per layer the count stays at zero (`NarrowChain.lean`).
-/
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.IntervalCases

namespace SquigglyLine

/-- One layer with two neurons: the tent `2 relu(x) - 4 relu(x - 1/2)`. -/
noncomputable def APPLY_TENT (x : ℝ) : ℝ :=
  2 * max x 0 - 4 * max (x - 1 / 2) 0

theorem tent_of_le_half {x : ℝ} (h0 : 0 ≤ x) (h : x ≤ 1 / 2) : APPLY_TENT x = 2 * x := by
  rw [APPLY_TENT, max_eq_left h0, max_eq_right (by linarith)]
  ring

theorem tent_of_half_le {x : ℝ} (h : 1 / 2 ≤ x) : APPLY_TENT x = 2 - 2 * x := by
  rw [APPLY_TENT, max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

/-- **Depth doubles the turns.** `L` tent layers send the `k`-th of `2 ^ L + 1` evenly spaced
inputs to 0 when `k` is even and to 1 when `k` is odd. -/
theorem iterate_tent_dyadic (L k : ℕ) (hk : k ≤ 2 ^ L) :
    APPLY_TENT^[L] ((k : ℝ) / 2 ^ L) = if Even k then 0 else 1 := by
  induction L generalizing k with
  | zero =>
    simp only [pow_zero] at hk
    interval_cases k <;> simp
  | succ L ih =>
    rw [Function.iterate_succ_apply]
    have hpow : (0 : ℝ) < 2 ^ L := by positivity
    rcases le_total k (2 ^ L) with hle | hge
    · have hkL : (k : ℝ) ≤ 2 ^ L := by exact_mod_cast hle
      have hhalf : (k : ℝ) / 2 ^ (L + 1) ≤ 1 / 2 := by
        rw [pow_succ, div_le_iff₀ (by positivity)]
        linarith
      have hx : APPLY_TENT ((k : ℝ) / 2 ^ (L + 1)) = (k : ℝ) / 2 ^ L := by
        rw [tent_of_le_half (by positivity) hhalf, pow_succ]
        field_simp
      rw [hx, ih k hle]
    · have hkL : (2 : ℝ) ^ L ≤ k := by exact_mod_cast hge
      have hk' : 2 ^ (L + 1) - k ≤ 2 ^ L := by
        rw [pow_succ]
        omega
      have hhalf : 1 / 2 ≤ (k : ℝ) / 2 ^ (L + 1) := by
        rw [pow_succ, le_div_iff₀ (by positivity)]
        linarith
      have hx : APPLY_TENT ((k : ℝ) / 2 ^ (L + 1)) = ((2 ^ (L + 1) - k : ℕ) : ℝ) / 2 ^ L := by
        rw [tent_of_half_le hhalf, Nat.cast_sub hk]
        push_cast
        rw [pow_succ]
        field_simp
      have hpar : Even (2 ^ (L + 1) - k) ↔ Even k := by
        rw [Nat.even_sub hk]
        simp [Nat.even_pow]
      rw [hx, ih _ hk']
      simp only [hpar]

end SquigglyLine
