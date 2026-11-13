/-
How fast attention merges the tokens.

`Attention.lean` shows that attention is an average, so it cannot spread the
tokens. This file gives a rate. If every score is at most `score_bound` in
size, every token gets a share of at least
`exp (-2 * score_bound) / card Tokens` of every query's attention. Two queries
then share that much of their averages, and what they disagree on is at most
the rest. So one layer shrinks the spread of the tokens by the factor
`1 - exp (-2 * score_bound)`, and `layer_count` layers by that factor to the
power `layer_count`.

The tokens here are numbers. Read them as one coordinate of the tokens, or
as any one read-out of them.

Theorems:

* `sum_mul_sub_sum_mul_le` : two averages with a common floor under their
  weights differ by at most the rest times the range of the values;
* `abs_sum_mul_sub_sum_mul_le` : the same, for the size of the difference;
* `exp_neg_div_card_le_softmax` : every token gets a share of the softmax;
* `abs_attend_sub_attend_le` : one layer shrinks the spread;
* `abs_iterate_attentionLayer_sub_le` : depth merges the tokens at a
  geometric rate.
-/
import SquigglyLine.Supporting.NetworkShape.Attention

namespace SquigglyLine

open Real

variable {Tokens : Type*} [Fintype Tokens]

/-- Two weighted averages whose weights all sit above a common floor differ by
at most the part they do not share times the range of the values. -/
theorem sum_mul_sub_sum_mul_le
    {weights other_weights values : Tokens → ℝ}
    {weight_floor lower_bound upper_bound : ℝ}
    (weights_above_floor : ∀ i, weight_floor ≤ weights i)
    (other_weights_above_floor : ∀ i, weight_floor ≤ other_weights i)
    (weights_sum_to_one : ∑ i, weights i = 1)
    (other_weights_sum_to_one : ∑ i, other_weights i = 1)
    (values_above_lower : ∀ i, lower_bound ≤ values i)
    (values_below_upper : ∀ i, values i ≤ upper_bound) :
    let average          := ∑ i, weights i * values i
    let other_average    := ∑ i, other_weights i * values i
    let gap              := average - other_average
    let disagreeable     := 1 - Fintype.card Tokens * weight_floor  -- `n * m` is shared, the rest can differ
    let value_range      := upper_bound - lower_bound
    gap ≤ disagreeable * value_range := by
  unfold_named_pieces
  -- Take the floor out of both. What is left of each has total weight
  -- `1 - n * weight_floor`.
  have leftover_sum :
      ∀ any_weights : Tokens → ℝ, ∑ i, any_weights i = 1 →
      ∑ i, (any_weights i - weight_floor)
        = 1 - Fintype.card Tokens * weight_floor := by
    intro any_weights any_weights_sum_to_one
    rw [Finset.sum_sub_distrib, any_weights_sum_to_one, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have leftover_upper :
      ∑ i, (weights i - weight_floor) * values i
        ≤ (1 - Fintype.card Tokens * weight_floor) * upper_bound := by
    rw [← leftover_sum weights weights_sum_to_one, Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (values_below_upper i)
        (sub_nonneg.mpr (weights_above_floor i))
  have leftover_lower :
      (1 - Fintype.card Tokens * weight_floor) * lower_bound
        ≤ ∑ i, (other_weights i - weight_floor) * values i := by
    rw [← leftover_sum other_weights other_weights_sum_to_one,
      Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (values_above_lower i)
        (sub_nonneg.mpr (other_weights_above_floor i))
  have gap_is_leftover_gap :
      ∑ i, weights i * values i - ∑ i, other_weights i * values i
        = ∑ i, (weights i - weight_floor) * values i
          - ∑ i, (other_weights i - weight_floor) * values i := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [gap_is_leftover_gap]
  linarith

/-- The same, for the size of the difference. -/
theorem abs_sum_mul_sub_sum_mul_le
    {weights other_weights values : Tokens → ℝ}
    {weight_floor lower_bound upper_bound : ℝ}
    (weights_above_floor : ∀ i, weight_floor ≤ weights i)
    (other_weights_above_floor : ∀ i, weight_floor ≤ other_weights i)
    (weights_sum_to_one : ∑ i, weights i = 1)
    (other_weights_sum_to_one : ∑ i, other_weights i = 1)
    (values_above_lower : ∀ i, lower_bound ≤ values i)
    (values_below_upper : ∀ i, values i ≤ upper_bound) :
    let average          := ∑ i, weights i * values i
    let other_average    := ∑ i, other_weights i * values i
    let gap_size         := |average - other_average|
    let disagreeable     := 1 - Fintype.card Tokens * weight_floor  -- `n * m` is shared, the rest can differ
    let value_range      := upper_bound - lower_bound
    gap_size ≤ disagreeable * value_range := by
  unfold_named_pieces
  rw [abs_le]
  constructor
  · -- Swap the two averages and use the one-sided bound.
    have swapped_gap :
        ∑ i, other_weights i * values i - ∑ i, weights i * values i
          ≤ (1 - Fintype.card Tokens * weight_floor)
            * (upper_bound - lower_bound) :=
      sum_mul_sub_sum_mul_le other_weights_above_floor weights_above_floor
        other_weights_sum_to_one weights_sum_to_one values_above_lower
        values_below_upper
    linarith
  · exact sum_mul_sub_sum_mul_le weights_above_floor other_weights_above_floor
      weights_sum_to_one other_weights_sum_to_one values_above_lower
      values_below_upper

variable [Nonempty Tokens]

/-- **Every token gets a share.** If every score is at most `score_bound` in
size, every share of the softmax is at least `exp (-2 * score_bound) / n`. -/
theorem exp_neg_div_card_le_softmax
    {scores : Tokens → ℝ}
    {score_bound : ℝ}
    (scores_are_bounded : ∀ i, |scores i| ≤ score_bound)
    (token : Tokens) :
    let smallest_share := exp (-2 * score_bound) / Fintype.card Tokens  -- `exp (-B)` over `n * exp B`
    let share          := APPLY_SOFTMAX scores token
    smallest_share ≤ share := by
  unfold_named_pieces
  have card_pos : (0 : ℝ) < Fintype.card Tokens := by
    exact_mod_cast Fintype.card_pos
  have total_le :
      ∑ j, exp (scores j) ≤ Fintype.card Tokens * exp score_bound := by
    calc ∑ j, exp (scores j) ≤ ∑ _j : Tokens, exp score_bound :=
          Finset.sum_le_sum fun j _ =>
            exp_le_exp.mpr (le_of_abs_le (scores_are_bounded j))
      _ = Fintype.card Tokens * exp score_bound := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have total_pos : 0 < ∑ j, exp (scores j) :=
    Finset.sum_pos (fun j _ => exp_pos (scores j)) Finset.univ_nonempty
  have smallest_exp_le : exp (-score_bound) ≤ exp (scores token) :=
    exp_le_exp.mpr (neg_le_of_abs_le (scores_are_bounded token))
  rw [APPLY_SOFTMAX, div_le_div_iff₀ card_pos total_pos]
  calc exp (-2 * score_bound) * ∑ j, exp (scores j)
      ≤ exp (-2 * score_bound) * (Fintype.card Tokens * exp score_bound) :=
        mul_le_mul_of_nonneg_left total_le (exp_pos _).le
    _ = exp (-score_bound) * Fintype.card Tokens := by
        rw [show -2 * score_bound = -score_bound + -score_bound by ring,
          exp_add]
        have exp_cancels : exp (-score_bound) * exp score_bound = 1 := by
          rw [← exp_add]
          simp
        calc exp (-score_bound) * exp (-score_bound)
              * (Fintype.card Tokens * exp score_bound)
            = exp (-score_bound) * Fintype.card Tokens
              * (exp (-score_bound) * exp score_bound) := by ring
          _ = exp (-score_bound) * Fintype.card Tokens := by
              rw [exp_cancels, mul_one]
    _ ≤ exp (scores token) * Fintype.card Tokens :=
        mul_le_mul_of_nonneg_right smallest_exp_le card_pos.le

/-- **One layer shrinks the spread.** Two queries whose scores are all at most
`score_bound` in size give answers that differ by at most
`1 - exp (-2 * score_bound)` times the range of the values. -/
theorem abs_attend_sub_attend_le
    {scores other_scores values : Tokens → ℝ}
    {score_bound lower_bound upper_bound : ℝ}
    (scores_are_bounded : ∀ i, |scores i| ≤ score_bound)
    (other_scores_are_bounded : ∀ i, |other_scores i| ≤ score_bound)
    (values_above_lower : ∀ i, lower_bound ≤ values i)
    (values_below_upper : ∀ i, values i ≤ upper_bound) :
    let answer        := ATTEND scores values
    let other_answer  := ATTEND other_scores values
    let disagreement  := |answer - other_answer|
    let shrink_factor := 1 - exp (-2 * score_bound)  -- `exp (-B)` is the smallest weight, `exp B` the largest
    let value_range   := upper_bound - lower_bound
    disagreement ≤ shrink_factor * value_range := by
  unfold_named_pieces
  have card_ne_zero : (Fintype.card Tokens : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have shared_bound :
      |∑ i, APPLY_SOFTMAX scores i * values i
          - ∑ i, APPLY_SOFTMAX other_scores i * values i|
        ≤ (1 - Fintype.card Tokens
            * (exp (-2 * score_bound) / Fintype.card Tokens))
          * (upper_bound - lower_bound) :=
    abs_sum_mul_sub_sum_mul_le
      (weights := APPLY_SOFTMAX scores)
      (other_weights := APPLY_SOFTMAX other_scores)
      (weight_floor := exp (-2 * score_bound) / Fintype.card Tokens)
      (exp_neg_div_card_le_softmax scores_are_bounded)
      (exp_neg_div_card_le_softmax other_scores_are_bounded)
      (sum_softmax scores) (sum_softmax other_scores)
      values_above_lower values_below_upper
  rw [mul_div_cancel₀ _ card_ne_zero] at shared_bound
  simpa [ATTEND] using shared_bound

/-- **Depth merges the tokens at a geometric rate.** With scores at most
`score_bound` in size at every layer, after `layer_count` layers of attention
any two tokens differ by at most
`(1 - exp (-2 * score_bound)) ^ layer_count` times the range they started
in. -/
theorem abs_iterate_attentionLayer_sub_le
    (score : TokenScorer Tokens ℝ)
    {score_bound : ℝ}
    (scores_are_bounded :
      ∀ any_tokens query token,
        |score any_tokens query token| ≤ score_bound)
    {tokens : Tokens → ℝ}
    {lower_bound upper_bound : ℝ}
    (tokens_above_lower : ∀ i, lower_bound ≤ tokens i)
    (tokens_below_upper : ∀ i, tokens i ≤ upper_bound)
    (layer_count : ℕ)
    (first_token second_token : Tokens) :
    let final_tokens  := (APPLY_ATTENTION_LAYER score)^[layer_count] tokens
    let disagreement  := |final_tokens first_token - final_tokens second_token|
    let shrink_factor := 1 - exp (-2 * score_bound)  -- one layer keeps this much of the spread
    let value_range   := upper_bound - lower_bound
    let shrunk_range  := shrink_factor ^ layer_count * value_range
    disagreement ≤ shrunk_range := by
  unfold_named_pieces
  have shrink_factor_nonneg : 0 ≤ 1 - exp (-2 * score_bound) := by
    have score_bound_nonneg : 0 ≤ score_bound :=
      (abs_nonneg _).trans (scores_are_bounded tokens first_token first_token)
    have exp_le_one : exp (-2 * score_bound) ≤ 1 := by
      rw [← exp_zero]
      exact exp_le_exp.mpr (by linarith)
    linarith
  -- Carry a range `[new_lower, new_upper]` of width at most
  -- `shrink_factor ^ layers * value_range` through the layers.
  have range_after : ∀ layers : ℕ, ∃ new_lower new_upper : ℝ,
      (∀ i, new_lower ≤ (APPLY_ATTENTION_LAYER score)^[layers] tokens i) ∧
      (∀ i, (APPLY_ATTENTION_LAYER score)^[layers] tokens i ≤ new_upper) ∧
      new_upper - new_lower
        ≤ (1 - exp (-2 * score_bound)) ^ layers
          * (upper_bound - lower_bound) := by
    intro layers
    induction layers with
    | zero =>
      exact ⟨lower_bound, upper_bound, tokens_above_lower,
        tokens_below_upper, by simp⟩
    | succ previous_layers range_before =>
      obtain ⟨old_lower, old_upper, tokens_above_old, tokens_below_old,
        old_width⟩ := range_before
      set old_tokens := (APPLY_ATTENTION_LAYER score)^[previous_layers] tokens
        with old_tokens_def
      -- The new tokens are answers to the queries; take the lowest and the
      -- highest.
      obtain ⟨lowest_token, -, lowest_is_lowest⟩ :=
        Finset.exists_min_image Finset.univ
          (fun token => APPLY_ATTENTION_LAYER score old_tokens token)
          Finset.univ_nonempty
      obtain ⟨highest_token, -, highest_is_highest⟩ :=
        Finset.exists_max_image Finset.univ
          (fun token => APPLY_ATTENTION_LAYER score old_tokens token)
          Finset.univ_nonempty
      refine ⟨APPLY_ATTENTION_LAYER score old_tokens lowest_token,
        APPLY_ATTENTION_LAYER score old_tokens highest_token, ?_, ?_, ?_⟩
      · intro token
        rw [Function.iterate_succ_apply']
        exact lowest_is_lowest token (Finset.mem_univ token)
      · intro token
        rw [Function.iterate_succ_apply']
        exact highest_is_highest token (Finset.mem_univ token)
      · -- One layer shrinks the range by the shrink factor.
        have gap_bound :
            |APPLY_ATTENTION_LAYER score old_tokens highest_token
                - APPLY_ATTENTION_LAYER score old_tokens lowest_token|
              ≤ (1 - exp (-2 * score_bound)) * (old_upper - old_lower) :=
          abs_attend_sub_attend_le
            (scores_are_bounded old_tokens highest_token)
            (scores_are_bounded old_tokens lowest_token)
            tokens_above_old tokens_below_old
        have gap_le := (le_abs_self _).trans gap_bound
        calc APPLY_ATTENTION_LAYER score old_tokens highest_token
              - APPLY_ATTENTION_LAYER score old_tokens lowest_token
            ≤ (1 - exp (-2 * score_bound)) * (old_upper - old_lower) :=
              gap_le
          _ ≤ (1 - exp (-2 * score_bound))
                * ((1 - exp (-2 * score_bound)) ^ previous_layers
                  * (upper_bound - lower_bound)) :=
              mul_le_mul_of_nonneg_left old_width shrink_factor_nonneg
          _ = (1 - exp (-2 * score_bound)) ^ (previous_layers + 1)
                * (upper_bound - lower_bound) := by ring
  obtain ⟨final_lower, final_upper, tokens_above_final, tokens_below_final,
    final_width⟩ := range_after layer_count
  rw [abs_le]
  constructor <;> linarith [tokens_above_final first_token,
    tokens_below_final first_token, tokens_above_final second_token,
    tokens_below_final second_token]

end SquigglyLine
