/-
Two facts about averages: the median, and random directions.

* **The median.** Squared error is least at the mean (`Averaging.lean`).
  Absolute error is least at a median: a value with at most half the points
  below it and at most half above.
* **Random directions are nearly at right angles, on average.** If the
  coordinates of a random direction are uncorrelated, each with mean square
  `s`, its overlap with a fixed direction `u` has mean square `s` times the
  squared length of `u`. With `s = 1 / d` and `u` of length one that is
  `1 / d`: the more dimensions, the smaller the overlap.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Theorems: `sum_abs_sub_le_of_le`, `sum_abs_sub_median_le`,
`sum_mul_sq_overlap`.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import SquigglyLine.Style

namespace SquigglyLine

variable {ι : Type*} [Fintype ι]

/-- Moving a centre up, away from a value that has at most half the points above it, does not
lower the summed absolute error. -/
theorem sum_abs_sub_le_of_le (x : ι → ℝ) {c d : ℝ}
    (habove : 2 * (Finset.univ.filter fun i => c < x i).card ≤ Fintype.card ι)
    (hcd : c ≤ d) :
    ∑ i, |x i - c| ≤ ∑ i, |x i - d| := by
  -- A point at or below `c` gets `d - c` further; a point above gets at most `d - c` nearer.
  have key : ∀ i, |x i - c| + (d - c) * (1 - 2 * (if c < x i then (1 : ℝ) else 0))
      ≤ |x i - d| := by
    intro i
    split_ifs with h <;>
      rcases abs_cases (x i - c) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
      rcases abs_cases (x i - d) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
      linarith
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
  have hcount : ∑ i, (if c < x i then (1 : ℝ) else 0)
      = ((Finset.univ.filter fun i => c < x i).card : ℝ) := by
    rw [Finset.sum_boole]
  have hsum : ∑ i, (d - c) * (1 - 2 * (if c < x i then (1 : ℝ) else 0))
      = (d - c) * (Fintype.card ι - 2 * (Finset.univ.filter fun i => c < x i).card) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hcount]
    simp
  rw [Finset.sum_add_distrib, hsum] at hs
  have hcast : (2 * (Finset.univ.filter fun i => c < x i).card : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast habove
  have hnonneg : 0 ≤ (d - c)
      * ((Fintype.card ι : ℝ) - 2 * (Finset.univ.filter fun i => c < x i).card) :=
    mul_nonneg (sub_nonneg.mpr hcd) (sub_nonneg.mpr hcast)
  linarith

/-- **Absolute error is least at a median.** If at most half the points are below `c` and at
most half are above it, no other centre has a smaller summed absolute error. -/
theorem sum_abs_sub_median_le (x : ι → ℝ) {c : ℝ}
    (hbelow : 2 * (Finset.univ.filter fun i => x i < c).card ≤ Fintype.card ι)
    (habove : 2 * (Finset.univ.filter fun i => c < x i).card ≤ Fintype.card ι) (d : ℝ) :
    ∑ i, |x i - c| ≤ ∑ i, |x i - d| := by
  rcases le_total c d with hcd | hdc
  · exact sum_abs_sub_le_of_le x habove hcd
  · -- Turn the line over: "below" becomes "above".
    have hflip : 2 * (Finset.univ.filter fun i => -c < -x i).card ≤ Fintype.card ι := by
      simpa using hbelow
    have h := sum_abs_sub_le_of_le (fun i => -x i) hflip (neg_le_neg hdc)
    have hrewrite : ∀ e : ℝ, ∑ i, |-x i - -e| = ∑ i, |x i - e| := fun e =>
      Finset.sum_congr rfl fun i _ => by rw [← abs_neg]; ring_nf
    rwa [hrewrite, hrewrite] at h

variable {Ω : Type*} [Fintype Ω] [DecidableEq ι]

/-- **Random directions are nearly at right angles, on average.** Let `v` be a random vector,
taking the value `v ω` with chance `p ω`, whose coordinates are uncorrelated with mean square
`s`. Its overlap with a fixed vector `u` has mean square `s` times the squared length of
`u`. -/
theorem sum_mul_sq_overlap {p : Ω → ℝ} {v : Ω → ι → ℝ} {s : ℝ}
    (hcov : ∀ i j, ∑ ω, p ω * (v ω i * v ω j) = if i = j then s else 0) (u : ι → ℝ) :
    ∑ ω, p ω * (∑ i, u i * v ω i) ^ 2 = s * ∑ i, u i ^ 2 := by
  have h1 : ∀ ω, p ω * (∑ i, u i * v ω i) ^ 2
      = ∑ i, ∑ j, u i * u j * (p ω * (v ω i * v ω j)) := by
    intro ω
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  calc ∑ ω, p ω * (∑ i, u i * v ω i) ^ 2
      = ∑ ω, ∑ i, ∑ j, u i * u j * (p ω * (v ω i * v ω j)) :=
        Finset.sum_congr rfl fun ω _ => h1 ω
    _ = ∑ i, ∑ j, ∑ ω, u i * u j * (p ω * (v ω i * v ω j)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, u i * u j * (if i = j then s else 0) := by
        simp only [← Finset.mul_sum, hcov]
    _ = s * ∑ i, u i ^ 2 := by
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring

end SquigglyLine
