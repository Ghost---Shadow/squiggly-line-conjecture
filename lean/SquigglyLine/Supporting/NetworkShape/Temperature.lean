/-
Temperature trades quality for diversity, and a codebook snaps to the nearest code.

* **Temperature.** Sample from a softmax of the scores times `β`, where `β`
  is one over the temperature. The average score of a sample never falls as
  `β` rises. So a colder sampler picks better-scoring answers on average.
  `one_sub_softmax_div_le` in `HardChoices.lean` is the other half: a cold
  softmax puts nearly all its share on the top score, so its samples are
  nearly all the same.
* **Codebook.** A codebook autoencoder replaces a code by the nearest entry
  of its codebook. The decoder's output moves by at most its slope times the
  distance to that entry, and no other entry would have moved it less far in
  the code. Snapping a second time changes nothing.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Theorems: `sum_mul_exp_mul_sum_exp_le`, `expectedScore_softmax_mono`,
`dist_decode_snap_le`, `dist_snap_le_of_nearest`.
-/
import SquigglyLine.Supporting.Training.CrossEntropy

namespace SquigglyLine

open Real NNReal

variable {ι : Type*} [Fintype ι]

/-- The cross-multiplied form of "the average score rises with `β`". -/
theorem sum_mul_exp_mul_sum_exp_le (z : ι → ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∑ i, z i * exp (a * z i)) * (∑ j, exp (b * z j))
      ≤ (∑ i, z i * exp (b * z i)) * (∑ j, exp (a * z j)) := by
  -- Pair every two answers. The better one gains more from a larger `β`.
  have key : ∀ i j, 0 ≤ (z i - z j)
      * (exp (b * z i + a * z j) - exp (a * z i + b * z j)) := by
    intro i j
    rcases le_total (z j) (z i) with h | h
    · refine mul_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (exp_le_exp.mpr ?_))
      nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr h)]
    · refine mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h)
        (sub_nonpos.mpr (exp_le_exp.mpr ?_))
      nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr h)]
  have hsum : 0 ≤ ∑ i, ∑ j, (z i - z j)
      * (exp (b * z i + a * z j) - exp (a * z i + b * z j)) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => key i j
  have hR : (∑ i, z i * exp (b * z i)) * (∑ j, exp (a * z j))
      = ∑ i, ∑ j, z i * exp (b * z i) * exp (a * z j) := Finset.sum_mul_sum _ _ _ _
  have hL : (∑ i, z i * exp (a * z i)) * (∑ j, exp (b * z j))
      = ∑ i, ∑ j, z i * exp (a * z i) * exp (b * z j) := Finset.sum_mul_sum _ _ _ _
  have hR' : (∑ i, z i * exp (b * z i)) * (∑ j, exp (a * z j))
      = ∑ i, ∑ j, z j * exp (b * z j) * exp (a * z i) := by
    rw [hR, Finset.sum_comm]
  have hL' : (∑ i, z i * exp (a * z i)) * (∑ j, exp (b * z j))
      = ∑ i, ∑ j, z j * exp (a * z j) * exp (b * z i) := by
    rw [hL, Finset.sum_comm]
  have hexpand : ∑ i, ∑ j, (z i - z j)
        * (exp (b * z i + a * z j) - exp (a * z i + b * z j))
      = ∑ i, ∑ j, (z i * exp (b * z i) * exp (a * z j) - z i * exp (a * z i) * exp (b * z j)
          - z j * exp (a * z j) * exp (b * z i) + z j * exp (b * z j) * exp (a * z i)) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [exp_add, exp_add]
    ring
  rw [hexpand] at hsum
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  rw [← hR, ← hL, ← hL', ← hR'] at hsum
  linarith

/-- **A colder sampler picks better answers on average.** With `β` one over the temperature,
the average score of a sample from the softmax never falls as `β` rises. -/
theorem expectedScore_softmax_mono [Nonempty ι] (z : ι → ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∑ i, APPLY_SOFTMAX (fun j => a * z j) i * z i
      ≤ ∑ i, APPLY_SOFTMAX (fun j => b * z j) i * z i := by
  have hpos : ∀ c : ℝ, 0 < ∑ j, exp (c * z j) := fun c =>
    Finset.sum_pos (fun j _ => exp_pos _) Finset.univ_nonempty
  have hform : ∀ c : ℝ, ∑ i, APPLY_SOFTMAX (fun j => c * z j) i * z i
      = (∑ i, z i * exp (c * z i)) / ∑ j, exp (c * z j) := by
    intro c
    simp only [APPLY_SOFTMAX]
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hform a, hform b, div_le_div_iff₀ (hpos a) (hpos b)]
  exact sum_mul_exp_mul_sum_exp_le z hab

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]

omit [Fintype ι] in
/-- **Snapping moves the output by at most slope times distance.** Replace a code by a
codebook entry. The decoder's output moves by at most its slope times how far the entry is. -/
theorem dist_decode_snap_le {decoder : E → F} {K : ℝ≥0} (hd : LipschitzWith K decoder)
    (code : E) (book : ι → E) (i : ι) :
    dist (decoder code) (decoder (book i)) ≤ K * dist code (book i) :=
  hd.dist_le_mul _ _

omit [Fintype ι] in
/-- **The nearest entry is the gentlest snap.** If entry `i` is the nearest, the output moves
by at most the slope times the distance to any entry. -/
theorem dist_snap_le_of_nearest {decoder : E → F} {K : ℝ≥0} (hd : LipschitzWith K decoder)
    (code : E) (book : ι → E) {i : ι} (hi : ∀ j, dist code (book i) ≤ dist code (book j))
    (j : ι) :
    dist (decoder code) (decoder (book i)) ≤ K * dist code (book j) :=
  (hd.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left (hi j) K.coe_nonneg)

end SquigglyLine
