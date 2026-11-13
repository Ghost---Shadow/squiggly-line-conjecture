/-
How fast attention merges the tokens.

`Attention.lean` shows that attention is an average, so it cannot spread the
tokens. This file gives a rate. If every score is at most `B` in size, every
token gets a share of at least `exp (-2 B) / n` of every query's attention.
Two queries then share that much of their averages, and what they disagree
on is at most the rest. So one layer shrinks the spread of the tokens by the
factor `1 - exp (-2 B)`, and `L` layers by that factor to the power `L`.

The tokens here are numbers. Read them as one coordinate of the tokens, or
as any one read-out of them.

Theorems: `sum_mul_sub_sum_mul_le`, `abs_sum_mul_sub_sum_mul_le`,
`exp_neg_div_card_le_softmax`, `abs_attend_sub_attend_le`,
`abs_iterate_attentionLayer_sub_le`.
-/
import SquigglyLine.Supporting.NetworkShape.Attention

namespace SquigglyLine

open Real

variable {ι : Type*} [Fintype ι]

/-- Two weighted averages whose weights all sit above a common floor `m` differ by at most
`1 - n m` times the range of the values. -/
theorem sum_mul_sub_sum_mul_le {p q v : ι → ℝ} {m lo hi : ℝ}
    (hp : ∀ i, m ≤ p i) (hq : ∀ i, m ≤ q i) (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1)
    (hlo : ∀ i, lo ≤ v i) (hhi : ∀ i, v i ≤ hi) :
    ∑ i, p i * v i - ∑ i, q i * v i ≤ (1 - Fintype.card ι * m) * (hi - lo) := by
  -- Take the floor out of both. What is left of each has total weight `1 - n m`.
  have hsum : ∀ w : ι → ℝ, ∑ i, w i = 1 → ∑ i, (w i - m) = 1 - Fintype.card ι * m := by
    intro w hw
    rw [Finset.sum_sub_distrib, hw, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hupper : ∑ i, (p i - m) * v i ≤ (1 - Fintype.card ι * m) * hi := by
    rw [← hsum p hp1, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hhi i) (sub_nonneg.mpr (hp i))
  have hlower : (1 - Fintype.card ι * m) * lo ≤ ∑ i, (q i - m) * v i := by
    rw [← hsum q hq1, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hlo i) (sub_nonneg.mpr (hq i))
  have hsplit : ∑ i, p i * v i - ∑ i, q i * v i
      = ∑ i, (p i - m) * v i - ∑ i, (q i - m) * v i := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  linarith

/-- The same, for the size of the difference. -/
theorem abs_sum_mul_sub_sum_mul_le {p q v : ι → ℝ} {m lo hi : ℝ}
    (hp : ∀ i, m ≤ p i) (hq : ∀ i, m ≤ q i) (hp1 : ∑ i, p i = 1) (hq1 : ∑ i, q i = 1)
    (hlo : ∀ i, lo ≤ v i) (hhi : ∀ i, v i ≤ hi) :
    |∑ i, p i * v i - ∑ i, q i * v i| ≤ (1 - Fintype.card ι * m) * (hi - lo) := by
  rw [abs_le]
  constructor
  · have h := sum_mul_sub_sum_mul_le hq hp hq1 hp1 hlo hhi
    linarith
  · exact sum_mul_sub_sum_mul_le hp hq hp1 hq1 hlo hhi

variable [Nonempty ι]

/-- **Every token gets a share.** If every score is at most `B` in size, every share of the
softmax is at least `exp (-2 B) / n`. -/
theorem exp_neg_div_card_le_softmax {z : ι → ℝ} {B : ℝ} (hz : ∀ i, |z i| ≤ B) (i : ι) :
    exp (-2 * B) / Fintype.card ι ≤ APPLY_SOFTMAX z i := by
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have htotal : ∑ j, exp (z j) ≤ Fintype.card ι * exp B := by
    calc ∑ j, exp (z j) ≤ ∑ _j : ι, exp B :=
          Finset.sum_le_sum fun j _ => exp_le_exp.mpr (le_of_abs_le (hz j))
      _ = Fintype.card ι * exp B := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hpos : 0 < ∑ j, exp (z j) :=
    Finset.sum_pos (fun j _ => exp_pos (z j)) Finset.univ_nonempty
  have hone : exp (-B) ≤ exp (z i) := exp_le_exp.mpr (neg_le_of_abs_le (hz i))
  rw [APPLY_SOFTMAX, div_le_div_iff₀ hcard hpos]
  calc exp (-2 * B) * ∑ j, exp (z j)
      ≤ exp (-2 * B) * (Fintype.card ι * exp B) :=
        mul_le_mul_of_nonneg_left htotal (exp_pos _).le
    _ = exp (-B) * Fintype.card ι := by
        rw [show -2 * B = -B + -B by ring, exp_add]
        have : exp (-B) * exp B = 1 := by rw [← exp_add]; simp
        calc exp (-B) * exp (-B) * (Fintype.card ι * exp B)
            = exp (-B) * Fintype.card ι * (exp (-B) * exp B) := by ring
          _ = exp (-B) * Fintype.card ι := by rw [this, mul_one]
    _ ≤ exp (z i) * Fintype.card ι := mul_le_mul_of_nonneg_right hone hcard.le

/-- **One layer shrinks the spread.** Two queries whose scores are all at most `B` in size
give answers that differ by at most `1 - exp (-2 B)` times the range of the values. -/
theorem abs_attend_sub_attend_le {z z' v : ι → ℝ} {B lo hi : ℝ}
    (hz : ∀ i, |z i| ≤ B) (hz' : ∀ i, |z' i| ≤ B)
    (hlo : ∀ i, lo ≤ v i) (hhi : ∀ i, v i ≤ hi) :
    |ATTEND z v - ATTEND z' v| ≤ (1 - exp (-2 * B)) * (hi - lo) := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h := abs_sum_mul_sub_sum_mul_le (m := exp (-2 * B) / Fintype.card ι)
    (exp_neg_div_card_le_softmax hz) (exp_neg_div_card_le_softmax hz')
    (sum_softmax z) (sum_softmax z') hlo hhi
  rw [mul_div_cancel₀ _ hcard] at h
  simpa [ATTEND] using h

/-- **Depth merges the tokens at a geometric rate.** With scores at most `B` in size at every
layer, after `L` layers of attention any two tokens differ by at most
`(1 - exp (-2 B)) ^ L` times the range they started in. -/
theorem abs_iterate_attentionLayer_sub_le (score : (ι → ℝ) → ι → ι → ℝ) {B : ℝ}
    (hscore : ∀ tokens i j, |score tokens i j| ≤ B) {tokens : ι → ℝ} {lo hi : ℝ}
    (hlo : ∀ i, lo ≤ tokens i) (hhi : ∀ i, tokens i ≤ hi) (L : ℕ) (i k : ι) :
    |(APPLY_ATTENTION_LAYER score)^[L] tokens i - (APPLY_ATTENTION_LAYER score)^[L] tokens k|
      ≤ (1 - exp (-2 * B)) ^ L * (hi - lo) := by
  have hr0 : 0 ≤ 1 - exp (-2 * B) := by
    have hB : 0 ≤ B := (abs_nonneg _).trans (hscore tokens i i)
    have : exp (-2 * B) ≤ 1 := by
      rw [← exp_zero]; exact exp_le_exp.mpr (by linarith)
    linarith
  -- Carry a range `[lo', hi']` of width at most `r ^ L * (hi - lo)` through the layers.
  have key : ∀ L : ℕ, ∃ lo' hi' : ℝ,
      (∀ i, lo' ≤ (APPLY_ATTENTION_LAYER score)^[L] tokens i) ∧
      (∀ i, (APPLY_ATTENTION_LAYER score)^[L] tokens i ≤ hi') ∧
      hi' - lo' ≤ (1 - exp (-2 * B)) ^ L * (hi - lo) := by
    intro L
    induction L with
    | zero => exact ⟨lo, hi, hlo, hhi, by simp⟩
    | succ L ih =>
      obtain ⟨lo', hi', hlo', hhi', hwidth⟩ := ih
      set x := (APPLY_ATTENTION_LAYER score)^[L] tokens with hx
      -- The new tokens are answers to the queries; take the lowest and the highest.
      obtain ⟨imin, -, hmin⟩ := Finset.exists_min_image Finset.univ
        (fun i => APPLY_ATTENTION_LAYER score x i) Finset.univ_nonempty
      obtain ⟨imax, -, hmax⟩ := Finset.exists_max_image Finset.univ
        (fun i => APPLY_ATTENTION_LAYER score x i) Finset.univ_nonempty
      refine ⟨APPLY_ATTENTION_LAYER score x imin, APPLY_ATTENTION_LAYER score x imax, ?_, ?_, ?_⟩
      · intro i; rw [Function.iterate_succ_apply']; exact hmin i (Finset.mem_univ i)
      · intro i; rw [Function.iterate_succ_apply']; exact hmax i (Finset.mem_univ i)
      · have hgap := abs_attend_sub_attend_le (hscore x imax) (hscore x imin) hlo' hhi'
        have hle := (le_abs_self _).trans hgap
        calc APPLY_ATTENTION_LAYER score x imax - APPLY_ATTENTION_LAYER score x imin
            ≤ (1 - exp (-2 * B)) * (hi' - lo') := hle
          _ ≤ (1 - exp (-2 * B)) * ((1 - exp (-2 * B)) ^ L * (hi - lo)) :=
              mul_le_mul_of_nonneg_left hwidth hr0
          _ = (1 - exp (-2 * B)) ^ (L + 1) * (hi - lo) := by ring
  obtain ⟨lo', hi', hlo', hhi', hwidth⟩ := key L
  rw [abs_le]
  constructor <;> linarith [hlo' i, hhi' i, hlo' k, hhi' k]

end SquigglyLine
