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
-/
import Mathlib.Analysis.Convex.Combination
import SquigglyLine.Supporting.NewInputs.SameKernel
import SquigglyLine.Supporting.Training.CrossEntropy

namespace SquigglyLine

open Real

/-! ### Attention as an average -/

section Average

variable {ι V : Type*} [Fintype ι] [Nonempty ι] [AddCommGroup V] [Module ℝ V]

/-- One attention head answering one query: the values of the tokens, averaged with the
softmax of their scores. -/
noncomputable def attend (score : ι → ℝ) (value : ι → V) : V :=
  ∑ i, softmax score i • value i

/-- **Attention averages.** Values inside a region with no dents give an output inside it. -/
theorem attend_mem_of_convex {region : Set V} (hregion : Convex ℝ region) (score : ι → ℝ)
    {value : ι → V} (hvalue : ∀ i, value i ∈ region) : attend score value ∈ region :=
  hregion.sum_mem (fun i _ => (softmax_pos score i).le) (sum_softmax score) fun i _ => hvalue i

/-- The output lies among the values. -/
theorem attend_mem_convexHull (score : ι → ℝ) (value : ι → V) :
    attend score value ∈ convexHull ℝ (Set.range value) :=
  attend_mem_of_convex (convex_convexHull ℝ _) score fun i =>
    subset_convexHull ℝ _ (Set.mem_range_self i)

/-- **Merged stays merged.** Tokens that all carry the value `v` give `v`, whatever the
scores. -/
theorem attend_const (score : ι → ℝ) (v : V) : attend score (fun _ => v) = v := by
  rw [attend, ← Finset.sum_smul, sum_softmax, one_smul]

/-- With equal scores every token gets the same share. -/
theorem softmax_const (c : ℝ) (i : ι) : softmax (fun _ : ι => c) i = (Fintype.card ι : ℝ)⁻¹ := by
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hexp := (exp_pos c).ne'
  simp only [softmax, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- **With equal scores, attention is the plain average.** -/
theorem attend_of_const_score (c : ℝ) (value : ι → V) :
    attend (fun _ => c) value = (Fintype.card ι : ℝ)⁻¹ • ∑ i, value i := by
  simp only [attend, softmax_const, Finset.smul_sum]

/-- A layer of attention: every token is a query. The scores may depend on the tokens in any
way. -/
noncomputable def attentionLayer (score : (ι → V) → ι → ι → ℝ) (tokens : ι → V) : ι → V :=
  fun query => attend (score tokens query) tokens

/-- **Attention alone never spreads the tokens.** After any number of layers, with any
scores, every token is still inside any dent-free region that held them all at the start. -/
theorem iterate_attentionLayer_mem {region : Set V} (hregion : Convex ℝ region)
    (score : (ι → V) → ι → ι → ℝ) {tokens : ι → V} (hstart : ∀ i, tokens i ∈ region) (depth : ℕ)
    (i : ι) : (attentionLayer score)^[depth] tokens i ∈ region := by
  induction depth generalizing i with
  | zero => exact hstart i
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact attend_mem_of_convex hregion _ ih

end Average

/-! ### Attention as learning -/

section InContext

open ContinuousLinearMap

variable {Θ Y : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- One step of gradient descent from zero weights predicts, at a new input with features
`q`, the labels weighted by the kernel between the data and `q`. -/
theorem inner_gradientStep_zero (A : Θ →L[ℝ] Y) (y : Y) (η : ℝ) (q : Θ) :
    inner ℝ q (gradientStep A y η 0) = η * inner ℝ (A q) y := by
  rw [inner_gradientStep]
  simp [residual]

variable {ι : Type*} [Fintype ι]

/-- Attention without the softmax: the values weighted by the raw scores. -/
def linearAttend (score value : ι → ℝ) : ℝ :=
  ∑ i, score i * value i

/-- **In-context learning.** Let the tokens be the examples. Score example `i` by its overlap
`A q i` with the query, and let its value be its label. Then one head of linear attention
gives the prediction of one step of gradient descent on those examples. -/
theorem prediction_one_step_eq_linearAttention (A : Θ →L[ℝ] EuclideanSpace ℝ ι)
    (y : EuclideanSpace ℝ ι) (η : ℝ) (q : Θ) :
    inner ℝ q (gradientStep A y η 0) = η * linearAttend (A q) y := by
  rw [inner_gradientStep_zero]
  simp [linearAttend, PiLp.inner_apply, mul_comm]

/-- **A further layer reads the errors.** From any weights, one more step changes the
prediction by the same head, with each example's value now the error still left on it. -/
theorem prediction_step_eq_linearAttention (A : Θ →L[ℝ] EuclideanSpace ℝ ι)
    (y : EuclideanSpace ℝ ι) (η : ℝ) (θ q : Θ) :
    inner ℝ q (gradientStep A y η θ)
      = inner ℝ q θ
        + η * linearAttend (A q) fun i => residual (A : Θ →ₗ[ℝ] EuclideanSpace ℝ ι) y θ i := by
  rw [inner_gradientStep]
  simp [linearAttend, PiLp.inner_apply, mul_comm]

end InContext

end SquigglyLine
