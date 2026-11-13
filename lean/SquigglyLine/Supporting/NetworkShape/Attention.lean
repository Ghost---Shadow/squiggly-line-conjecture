/-
Attention: a weighted average, and one step of training.

An attention head scores every token against a query, turns the scores into
shares with a softmax, and returns the values of the tokens averaged with
those shares.

Attention as an average:
* `attend_mem_convexHull` : the output lies among the values.
* `attend_mem_of_convex` : values inside a region with no dents stay inside.
* `attend_const` : tokens that carry the same value come out with that value.
* `attend_of_const_score` : with equal scores it is the plain average.
* `iterate_attentionLayer_mem` : so any number of attention layers, with any
  scores, keep every token inside the region the tokens started in.

Attention as learning:
* `inner_gradientStep_zero` : one step of gradient descent from zero weights
  predicts the labels weighted by the kernel between the query and the data.
* `prediction_one_step_eq_linearAttention` : that is an attention head
  without the softmax, with the examples as tokens and their labels as values.
* `prediction_step_eq_linearAttention` : a further step is the same head
  reading the errors left so far.

Definitions: `ATTEND`, `APPLY_ATTENTION_LAYER`, `ATTEND_LINEARLY`.
Theorems also include `softmax_const` : equal scores give equal shares.
-/
import Mathlib.Analysis.Convex.Combination
import SquigglyLine.Supporting.NewInputs.SameKernel
import SquigglyLine.Supporting.Training.CrossEntropy

namespace SquigglyLine

open Real

/-- A rule that scores every token against every query, and may look at all
the tokens to do so.
Python: `Callable[[list[Value]], list[list[float]]]`. -/
abbrev TokenScorer (Tokens Values : Type*) :=
  (Tokens → Values) → Tokens → Tokens → ℝ

/-! ### Attention as an average -/

section Average

variable {Tokens Values : Type*} [Fintype Tokens] [Nonempty Tokens]
  [AddCommGroup Values] [Module ℝ Values]

/-- One attention head answering one query: the values of the tokens,
averaged with the softmax of their scores.
Python: `sum(softmax(score)[i] * value[i] for i in tokens)`. -/
noncomputable def ATTEND
    (score : Tokens → ℝ)
    (value : Tokens → Values) : Values :=
  ∑ i, APPLY_SOFTMAX score i • value i

/-- **Attention averages.** Values inside a region with no dents give an
output inside it. -/
theorem attend_mem_of_convex
    {region : Set Values}
    (region_is_convex : Convex ℝ region)
    (score : Tokens → ℝ)
    {value : Tokens → Values}
    (values_in_region : ∀ i, value i ∈ region) :
    let output := ATTEND score value
    output ∈ region := by
  unfold_named_pieces
  exact region_is_convex.sum_mem (fun i _ => (softmax_pos score i).le)
    (sum_softmax score) fun i _ => values_in_region i

/-- The output lies among the values. -/
theorem attend_mem_convexHull
    (score : Tokens → ℝ)
    (value : Tokens → Values) :
    let output := ATTEND score value
    let hull   := convexHull ℝ (Set.range value)
    output ∈ hull := by
  unfold_named_pieces
  exact attend_mem_of_convex (convex_convexHull ℝ _) score fun i =>
    subset_convexHull ℝ _ (Set.mem_range_self i)

/-- **Merged stays merged.** Tokens that all carry the value `shared_value`
give `shared_value`, whatever the scores. -/
theorem attend_const
    (score : Tokens → ℝ)
    (shared_value : Values) :
    let same_values : Tokens → Values := fun _ => shared_value
    let output                        := ATTEND score same_values
    output = shared_value := by
  unfold_named_pieces
  rw [ATTEND, ← Finset.sum_smul, sum_softmax, one_smul]

/-- With equal scores every token gets the same share. -/
theorem softmax_const
    (equal_score : ℝ)
    (chosen_token : Tokens) :
    let scores : Tokens → ℝ := fun _ => equal_score
    let share         := APPLY_SOFTMAX scores chosen_token
    let uniform_share := (Fintype.card Tokens : ℝ)⁻¹  -- one share out of `card` equal ones
    share = uniform_share := by
  unfold_named_pieces
  have token_count_ne_zero : (Fintype.card Tokens : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have exp_score_ne_zero := (exp_pos equal_score).ne'
  simp only [APPLY_SOFTMAX, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp

/-- **With equal scores, attention is the plain average.** -/
theorem attend_of_const_score
    (equal_score : ℝ)
    (value : Tokens → Values) :
    let scores : Tokens → ℝ := fun _ => equal_score
    let output        := ATTEND scores value
    let plain_average := (Fintype.card Tokens : ℝ)⁻¹ • ∑ i, value i
    output = plain_average := by
  unfold_named_pieces
  have equal_shares (i : Tokens) :
      APPLY_SOFTMAX (fun _ : Tokens => equal_score) i
        = (Fintype.card Tokens : ℝ)⁻¹ :=
    softmax_const equal_score i
  simp only [ATTEND, equal_shares, Finset.smul_sum]

/-- A layer of attention: every token is a query. The scores may depend on
the tokens in any way. -/
noncomputable def APPLY_ATTENTION_LAYER
    (score : TokenScorer Tokens Values)
    (tokens : Tokens → Values) : Tokens → Values :=
  fun query => ATTEND (score tokens query) tokens

/-- **Attention alone never spreads the tokens.** After any number of layers,
with any scores, every token is still inside any dent-free region that held
them all at the start. -/
theorem iterate_attentionLayer_mem
    {region : Set Values}
    (region_is_convex : Convex ℝ region)
    (score : TokenScorer Tokens Values)
    {tokens : Tokens → Values}
    (tokens_in_region : ∀ i, tokens i ∈ region)
    (depth : ℕ)
    (query : Tokens) :
    let final_tokens := (APPLY_ATTENTION_LAYER score)^[depth] tokens
    final_tokens query ∈ region := by
  unfold_named_pieces
  induction depth generalizing query with
  | zero => exact tokens_in_region query
  | succ previous_depth previous_in_region =>
    -- One more layer is an average of the tokens one layer earlier.
    rw [Function.iterate_succ_apply']
    exact attend_mem_of_convex region_is_convex _ previous_in_region

end Average

/-! ### Attention as learning -/

section InContext

open ContinuousLinearMap

variable {Weights Outputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]

/-- One step of gradient descent from zero weights predicts, at a new input
with features `query_features`, the labels weighted by the kernel between the
data and `query_features`. -/
theorem inner_gradientStep_zero
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (query_features : Weights) :
    let prediction :=
      inner ℝ query_features
        (TAKE_GRADIENT_STEP predict labels learning_rate 0)
    let kernel_weighted_labels :=
      learning_rate * inner ℝ (predict query_features) labels
    prediction = kernel_weighted_labels := by
  unfold_named_pieces
  rw [inner_gradientStep]
  simp [GET_RESIDUAL]

variable {Examples : Type*} [Fintype Examples]

/-- Attention without the softmax: the values weighted by the raw scores.
Python: `sum(score[i] * value[i] for i in examples)`. -/
def ATTEND_LINEARLY
    (score : Examples → ℝ)
    (value : Examples → ℝ) : ℝ :=
  ∑ i, score i * value i

/-- **In-context learning.** Let the tokens be the examples. Score example `i`
by its overlap `predict query_features i` with the query, and let its value be
its label. Then one head of linear attention gives the prediction of one step
of gradient descent on those examples. -/
theorem prediction_one_step_eq_linearAttention
    (predict : Weights →L[ℝ] ExampleScores Examples)
    (labels : ExampleScores Examples)
    (learning_rate : ℝ)
    (query_features : Weights) :
    let prediction :=
      inner ℝ query_features
        (TAKE_GRADIENT_STEP predict labels learning_rate 0)
    let head_output :=
      learning_rate * ATTEND_LINEARLY (predict query_features) labels
    prediction = head_output := by
  unfold_named_pieces
  rw [inner_gradientStep_zero]
  simp [ATTEND_LINEARLY, PiLp.inner_apply, mul_comm]

/-- **A further layer reads the errors.** From any weights, one more step
changes the prediction by the same head, with each example's value now the
error still left on it. -/
theorem prediction_step_eq_linearAttention
    (predict : Weights →L[ℝ] ExampleScores Examples)
    (labels : ExampleScores Examples)
    (learning_rate : ℝ)
    (weights : Weights)
    (query_features : Weights) :
    let new_prediction :=
      inner ℝ query_features
        (TAKE_GRADIENT_STEP predict labels learning_rate weights)
    let old_prediction := inner ℝ query_features weights
    let head_output :=
      learning_rate * ATTEND_LINEARLY (predict query_features) fun i =>
        GET_RESIDUAL (predict : Weights →ₗ[ℝ] ExampleScores Examples)
          labels weights i
    new_prediction = old_prediction + head_output := by
  unfold_named_pieces
  rw [inner_gradientStep]
  simp [ATTEND_LINEARLY, PiLp.inner_apply, mul_comm]

end InContext

end SquigglyLine
