/-
Gates, codes and a narrow last layer.

* **Mixture of experts.** A gate blends several experts. The blend's output
  changes by at most what the experts change, plus the spread of the experts
  times how much the gate changes. Where the experts agree, the gate adds no
  slope.
* **The penalty of a variational autoencoder.** For a code drawn from a bell
  curve of centre `centre` and width `width`, the penalty is
  `(centre² + width² - 1 - log width²) / 2`. It is at least half the squared
  distance of the centre from the origin, and zero only for the code that
  ignores its input.
* **The softmax bottleneck.** A table of scores made from `hidden_size`
  hidden numbers per row has rank at most `hidden_size`, so with more rows
  than that it cannot be every table.

| Name                | Meaning                                              |
|---------------------|------------------------------------------------------|
| `HiddenVectors`     | one row of hidden numbers for each item              |
| `GET_CODE_PENALTY`  | the penalty of a code of a given centre and width    |

Theorems: `abs_mixture_sub_le`, `half_sq_le_codePenalty`,
`codePenalty_nonneg`, `codePenalty_eq_zero_iff`, `rank_scoreTable_le`,
`scoreTable_ne_one`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import SquigglyLine.Style

namespace SquigglyLine

open Real

variable {Expert : Type*} [Fintype Expert]

/-- **A gate adds slope only through the spread of the experts.** Blend the
experts' outputs with gates that are not negative and add to one. Between two
inputs, the blend changes by at most `max_expert_change`, the most any expert
changes, plus the spread `high - low` of the experts times the total change in
the gates. -/
theorem abs_mixture_sub_le
    {gates : Expert → ℝ}
    {other_gates : Expert → ℝ}
    {outputs : Expert → ℝ}
    {other_outputs : Expert → ℝ}
    {max_expert_change : ℝ}
    {low : ℝ}
    {high : ℝ}
    (gates_nonneg : ∀ i, 0 ≤ gates i)
    (gates_sum_to_one : ∑ i, gates i = 1)
    (other_gates_sum_to_one : ∑ i, other_gates i = 1)
    (experts_change_little :
      ∀ i, |outputs i - other_outputs i| ≤ max_expert_change)
    (outputs_above_low : ∀ i, low ≤ other_outputs i)
    (outputs_below_high : ∀ i, other_outputs i ≤ high) :
    let blend         := ∑ i, gates i * outputs i
    let other_blend   := ∑ i, other_gates i * other_outputs i
    let blend_change  := |blend - other_blend|
    let spread        := high - low
    let gate_change   := ∑ i, |gates i - other_gates i|
    let change_limit  := max_expert_change + spread * gate_change
    blend_change ≤ change_limit := by
  unfold_named_pieces
  -- Split: the experts move under fixed gates, then the gates move over fixed
  -- experts.
  have blend_split :
      ∑ i, gates i * outputs i - ∑ i, other_gates i * other_outputs i
        = ∑ i, gates i * (outputs i - other_outputs i)
          + ∑ i, (gates i - other_gates i) * (other_outputs i - low) := by
    -- Shifting every output by `low` costs nothing: both gates add to one.
    have shift_is_zero : ∑ i, (gates i - other_gates i) * low = 0 := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, gates_sum_to_one,
        other_gates_sum_to_one, sub_self, zero_mul]
    have term_split : ∀ i,
        gates i * (outputs i - other_outputs i)
          + (gates i - other_gates i) * (other_outputs i - low)
        = gates i * outputs i - other_gates i * other_outputs i
          - (gates i - other_gates i) * low := fun i => by ring
    rw [← Finset.sum_add_distrib]
    simp only [term_split, Finset.sum_sub_distrib, shift_is_zero, sub_zero]
  have experts_part :
      |∑ i, gates i * (outputs i - other_outputs i)|
        ≤ max_expert_change := by
    calc |∑ i, gates i * (outputs i - other_outputs i)|
        ≤ ∑ i, |gates i * (outputs i - other_outputs i)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, gates i * max_expert_change := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, abs_of_nonneg (gates_nonneg i)]
          exact mul_le_mul_of_nonneg_left (experts_change_little i)
            (gates_nonneg i)
      _ = max_expert_change := by
          rw [← Finset.sum_mul, gates_sum_to_one, one_mul]
  have gates_part :
      |∑ i, (gates i - other_gates i) * (other_outputs i - low)|
        ≤ (high - low) * ∑ i, |gates i - other_gates i| := by
    calc |∑ i, (gates i - other_gates i) * (other_outputs i - low)|
        ≤ ∑ i, |(gates i - other_gates i) * (other_outputs i - low)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |gates i - other_gates i| * (high - low) := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr (outputs_above_low i))]
          exact mul_le_mul_of_nonneg_left
            (by linarith [outputs_below_high i]) (abs_nonneg _)
      _ = (high - low) * ∑ i, |gates i - other_gates i| := by
          rw [← Finset.sum_mul, mul_comm]
  rw [blend_split]
  exact (abs_add_le _ _).trans (add_le_add experts_part gates_part)

/-- The penalty a variational autoencoder puts on a code drawn from a bell
curve of centre `centre` and width `width`: its distance, in the sense of
coding, from the standard bell curve.
Python: `(centre ** 2 + width ** 2 - 1 - log(width ** 2)) / 2`. -/
noncomputable def GET_CODE_PENALTY
    (centre : ℝ)
    (width : ℝ) : ℝ :=
  (centre ^ 2 + width ^ 2 - 1 - log (width ^ 2)) / 2

/-- **The penalty charges for travel.** It is at least half the squared
distance of the code's centre from the origin. -/
theorem half_sq_le_codePenalty
    (centre : ℝ)
    {width : ℝ}
    (width_ne_zero : width ≠ 0) :
    let half_squared_centre := centre ^ 2 / 2
    let penalty             := GET_CODE_PENALTY centre width
    half_squared_centre ≤ penalty := by
  unfold_named_pieces
  have width_sq_pos : 0 < width ^ 2 := by positivity
  -- `log x ≤ x - 1`.
  have log_le : log (width ^ 2) ≤ width ^ 2 - 1 :=
    log_le_sub_one_of_pos width_sq_pos
  rw [GET_CODE_PENALTY]
  linarith

/-- The penalty is never negative. -/
theorem codePenalty_nonneg
    (centre : ℝ)
    {width : ℝ}
    (width_ne_zero : width ≠ 0) :
    let penalty := GET_CODE_PENALTY centre width
    let no_penalty : ℝ := 0
    no_penalty ≤ penalty := by
  unfold_named_pieces
  have half_sq_le : centre ^ 2 / 2 ≤ GET_CODE_PENALTY centre width :=
    half_sq_le_codePenalty centre width_ne_zero
  exact (by positivity : (0 : ℝ) ≤ centre ^ 2 / 2).trans half_sq_le

/-- **It is zero only for the code that ignores its input**: centre zero and
width one, the same for every input. -/
theorem codePenalty_eq_zero_iff
    (centre : ℝ)
    {width : ℝ}
    (width_ne_zero : width ≠ 0) :
    let penalty            := GET_CODE_PENALTY centre width
    let penalty_is_zero    := penalty = 0
    let centre_is_zero     := centre = 0
    let width_is_one       := width ^ 2 = 1
    let code_ignores_input := centre_is_zero ∧ width_is_one
    penalty_is_zero ↔ code_ignores_input := by
  unfold_named_pieces
  have width_sq_pos : 0 < width ^ 2 := by positivity
  constructor
  · intro penalty_zero
    have log_le : log (width ^ 2) ≤ width ^ 2 - 1 :=
      log_le_sub_one_of_pos width_sq_pos
    rw [GET_CODE_PENALTY] at penalty_zero
    have centre_sq_zero : centre ^ 2 = 0 := by
      nlinarith [sq_nonneg centre]
    have centre_zero : centre = 0 := by simpa using centre_sq_zero
    refine ⟨centre_zero, ?_⟩
    -- If the width were not one, the logarithm bound would be strict.
    by_contra width_sq_ne_one
    have log_lt : log (width ^ 2) < width ^ 2 - 1 :=
      log_lt_sub_one_of_pos width_sq_pos width_sq_ne_one
    rw [centre_zero] at penalty_zero
    linarith
  · rintro ⟨rfl, width_sq_one⟩
    rw [GET_CODE_PENALTY, width_sq_one]
    simp

/-- One row of hidden numbers for each item of a finite set.
Python: `numpy.ndarray` of shape `(len(items), hidden_size)`. -/
abbrev HiddenVectors
    (Item : Type*)
    (hidden_size : ℕ) := Matrix Item (Fin hidden_size) ℝ

variable {Context Word : Type*} [Fintype Context] [Fintype Word]
  {hidden_size : ℕ}

omit [Fintype Context] in
/-- **The softmax bottleneck.** A table of scores, one row per context and one
column per word, made from `hidden_size` hidden numbers per context and
`hidden_size` per word, has rank at most `hidden_size`. -/
theorem rank_scoreTable_le
    (context_vectors : HiddenVectors Context hidden_size)
    (word_vectors : HiddenVectors Word hidden_size) :
    let score_table := context_vectors * word_vectors.transpose
    let table_rank  := score_table.rank
    table_rank ≤ hidden_size := by
  unfold_named_pieces
  calc (context_vectors * word_vectors.transpose).rank
      ≤ context_vectors.rank := Matrix.rank_mul_le_left _ _
    _ ≤ Fintype.card (Fin hidden_size) := Matrix.rank_le_card_width _
    _ = hidden_size := Fintype.card_fin hidden_size

/-- So with more contexts than hidden numbers, some table cannot be made: for
one, the table that scores each context's own word one and every other word
zero. -/
theorem scoreTable_ne_one
    {context_count : ℕ}
    (hidden_size_lt : hidden_size < context_count)
    (context_vectors : HiddenVectors (Fin context_count) hidden_size)
    (word_vectors : HiddenVectors (Fin context_count) hidden_size) :
    let score_table := context_vectors * word_vectors.transpose
    let identity_table : Matrix (Fin context_count) (Fin context_count) ℝ := 1  -- one on the diagonal, zero elsewhere
    score_table ≠ identity_table := by
  unfold_named_pieces
  intro same_table
  have rank_bound :
      (context_vectors * word_vectors.transpose).rank ≤ hidden_size :=
    rank_scoreTable_le context_vectors word_vectors
  rw [same_table, Matrix.rank_one, Fintype.card_fin] at rank_bound
  omega

end SquigglyLine
