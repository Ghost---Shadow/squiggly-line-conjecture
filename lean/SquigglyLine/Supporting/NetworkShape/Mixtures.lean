/-
Gates, codes and a narrow last layer.

* **Mixture of experts.** A gate blends several experts. The blend's output
  changes by at most what the experts change, plus the spread of the experts
  times how much the gate changes. Where the experts agree, the gate adds no
  slope.
* **The penalty of a variational autoencoder.** For a code drawn from a bell
  curve of centre `μ` and width `σ`, the penalty is
  `(μ² + σ² - 1 - log σ²) / 2`. It is at least half the squared distance of
  the centre from the origin, and zero only for the code that ignores its
  input.
* **The softmax bottleneck.** A table of scores made from `d` hidden numbers
  per row has rank at most `d`, so with more rows than `d` it cannot be every
  table.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Definitions: `GET_CODE_PENALTY`.

Theorems: `abs_mixture_sub_le`, `half_sq_le_codePenalty`,
`codePenalty_nonneg`, `codePenalty_eq_zero_iff`, `rank_scoreTable_le`,
`scoreTable_ne_one`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import SquigglyLine.Style

namespace SquigglyLine

open Real

variable {ι : Type*} [Fintype ι]

/-- **A gate adds slope only through the spread of the experts.** Blend the experts `f i` with
gates that are not negative and add to one. Between two inputs, the blend changes by at most
`D`, the most any expert changes, plus the spread `hi - lo` of the experts times the total
change in the gates. -/
theorem abs_mixture_sub_le {gx gy fx fy : ι → ℝ} {D lo hi : ℝ}
    (hgx : ∀ i, 0 ≤ gx i) (hgx1 : ∑ i, gx i = 1) (hgy1 : ∑ i, gy i = 1)
    (hD : ∀ i, |fx i - fy i| ≤ D) (hlo : ∀ i, lo ≤ fy i) (hhi : ∀ i, fy i ≤ hi) :
    |∑ i, gx i * fx i - ∑ i, gy i * fy i| ≤ D + (hi - lo) * ∑ i, |gx i - gy i| := by
  -- Split: the experts move under fixed gates, then the gates move over fixed experts.
  have hsplit : ∑ i, gx i * fx i - ∑ i, gy i * fy i
      = ∑ i, gx i * (fx i - fy i) + ∑ i, (gx i - gy i) * (fy i - lo) := by
    have hzero : ∑ i, (gx i - gy i) * lo = 0 := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, hgx1, hgy1, sub_self, zero_mul]
    have hterm : ∀ i, gx i * (fx i - fy i) + (gx i - gy i) * (fy i - lo)
        = gx i * fx i - gy i * fy i - (gx i - gy i) * lo := fun i => by ring
    rw [← Finset.sum_add_distrib]
    simp only [hterm, Finset.sum_sub_distrib, hzero, sub_zero]
  have h1 : |∑ i, gx i * (fx i - fy i)| ≤ D := by
    calc |∑ i, gx i * (fx i - fy i)|
        ≤ ∑ i, |gx i * (fx i - fy i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, gx i * D := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, abs_of_nonneg (hgx i)]
          exact mul_le_mul_of_nonneg_left (hD i) (hgx i)
      _ = D := by rw [← Finset.sum_mul, hgx1, one_mul]
  have h2 : |∑ i, (gx i - gy i) * (fy i - lo)| ≤ (hi - lo) * ∑ i, |gx i - gy i| := by
    calc |∑ i, (gx i - gy i) * (fy i - lo)|
        ≤ ∑ i, |(gx i - gy i) * (fy i - lo)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |gx i - gy i| * (hi - lo) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (hlo i))]
          exact mul_le_mul_of_nonneg_left (by linarith [hhi i]) (abs_nonneg _)
      _ = (hi - lo) * ∑ i, |gx i - gy i| := by rw [← Finset.sum_mul, mul_comm]
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- The penalty a variational autoencoder puts on a code drawn from a bell curve of centre `μ`
and width `σ`: its distance, in the sense of coding, from the standard bell curve.
Python: `(μ ** 2 + σ ** 2 - 1 - log(σ ** 2)) / 2`. -/
noncomputable def GET_CODE_PENALTY (μ σ : ℝ) : ℝ :=
  (μ ^ 2 + σ ^ 2 - 1 - log (σ ^ 2)) / 2

/-- **The penalty charges for travel.** It is at least half the squared distance of the code's
centre from the origin. -/
theorem half_sq_le_codePenalty (μ : ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    μ ^ 2 / 2 ≤ GET_CODE_PENALTY μ σ := by
  have hpos : 0 < σ ^ 2 := by positivity
  have hlog : log (σ ^ 2) ≤ σ ^ 2 - 1 := log_le_sub_one_of_pos hpos
  rw [GET_CODE_PENALTY]
  linarith

theorem codePenalty_nonneg (μ : ℝ) {σ : ℝ} (hσ : σ ≠ 0) : 0 ≤ GET_CODE_PENALTY μ σ :=
  (by positivity : (0 : ℝ) ≤ μ ^ 2 / 2).trans (half_sq_le_codePenalty μ hσ)

/-- **It is zero only for the code that ignores its input**: centre zero and width one, the
same for every input. -/
theorem codePenalty_eq_zero_iff (μ : ℝ) {σ : ℝ} (hσ : σ ≠ 0) :
    GET_CODE_PENALTY μ σ = 0 ↔ μ = 0 ∧ σ ^ 2 = 1 := by
  have hpos : 0 < σ ^ 2 := by positivity
  constructor
  · intro h
    have hlog : log (σ ^ 2) ≤ σ ^ 2 - 1 := log_le_sub_one_of_pos hpos
    rw [GET_CODE_PENALTY] at h
    have hμ : μ ^ 2 = 0 := by nlinarith [sq_nonneg μ]
    have hμ0 : μ = 0 := by simpa using hμ
    refine ⟨hμ0, ?_⟩
    by_contra hne
    have hstrict : log (σ ^ 2) < σ ^ 2 - 1 := log_lt_sub_one_of_pos hpos hne
    rw [hμ0] at h
    linarith
  · rintro ⟨rfl, h1⟩
    rw [GET_CODE_PENALTY, h1]
    simp

variable {C W : Type*} [Fintype C] [Fintype W] {d : ℕ}

omit [Fintype C] in
/-- **The softmax bottleneck.** A table of scores, one row per context and one column per
word, made from `d` hidden numbers per context and `d` per word, has rank at most `d`. -/
theorem rank_scoreTable_le (H : Matrix C (Fin d) ℝ) (E : Matrix W (Fin d) ℝ) :
    (H * E.transpose).rank ≤ d := by
  calc (H * E.transpose).rank ≤ H.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin d) := Matrix.rank_le_card_width _
    _ = d := Fintype.card_fin d

/-- So with more contexts than hidden numbers, some table cannot be made: for one, the table
that scores each context's own word one and every other word zero. -/
theorem scoreTable_ne_one {n : ℕ} (hd : d < n) (H E : Matrix (Fin n) (Fin d) ℝ) :
    H * E.transpose ≠ 1 := by
  intro h
  have hrank := rank_scoreTable_le H E
  rw [h, Matrix.rank_one, Fintype.card_fin] at hrank
  omega

end SquigglyLine
