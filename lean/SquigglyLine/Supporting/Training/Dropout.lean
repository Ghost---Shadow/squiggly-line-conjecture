/-
Dropout is weight decay.

Dropout multiplies each feature by a random mask during training. The mask
is one on average, so the model's answer is right on average and noisy
around that.

* `expected_dropout_loss` : for one example, the expected squared error under
  dropout is the plain squared error plus a penalty: the variance of the mask
  times the sum of the squared shares "feature times weight".
* `expected_dropout_loss_dataset` : over a set of examples the penalty on
  weight `j` is its square times the total squared size of feature `j`.
* `expected_dropout_loss_of_equal_features` : when every feature has the same
  total squared size `c`, the penalty is `v c` times the squared length of
  the weights. That is weight decay.
* `keepMask_variance` : the usual mask, kept with probability `p` and scaled
  by `1 / p`, has variance `(1 - p) / p`.
-/
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace SquigglyLine

open MeasureTheory ProbabilityTheory

/-- The usual dropout mask is `1 / p` with probability `p` and `0` otherwise. Its mean is one
and its variance, written out over the two outcomes, is `(1 - p) / p`. -/
theorem keepMask_variance {p : ℝ} (hp : p ≠ 0) :
    p * (1 / p - 1) ^ 2 + (1 - p) * (0 - 1) ^ 2 = (1 - p) / p := by
  field_simp
  ring

section Expectation

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  {ι : Type*} [Fintype ι]

/-- **Dropout adds a penalty.** One example with label `y`. Feature `j` contributes the
share `a j` (the feature times its weight) to the answer, and dropout multiplies it by
`mask j`. If the masks are independent, one on average and of variance `v`, the expected
squared error is the plain squared error plus `v` times the sum of the squared shares. -/
theorem expected_dropout_loss {mask : ι → Ω → ℝ} (hsquare : ∀ j, MemLp (mask j) 2 P)
    (hindep : Pairwise fun i j => mask i ⟂ᵢ[P] mask j) (hmean : ∀ j, ∫ ω, mask j ω ∂P = 1)
    {v : ℝ} (hvar : ∀ j, variance (mask j) P = v) (y : ℝ) (a : ι → ℝ) :
    ∫ ω, (y - ∑ j, mask j ω * a j) ^ 2 ∂P = (y - ∑ j, a j) ^ 2 + v * ∑ j, a j ^ 2 := by
  have hterm (j : ι) : MemLp (fun ω => mask j ω * a j) 2 P := (hsquare j).mul_const (a j)
  have hanswerFn : (fun ω => ∑ j, mask j ω * a j) = ∑ j, fun ω => mask j ω * a j := by
    ext ω
    simp
  have hanswer : MemLp (fun ω => ∑ j, mask j ω * a j) 2 P :=
    memLp_finsetSum _ fun j _ => hterm j
  have hmeanAnswer : ∫ ω, ∑ j, mask j ω * a j ∂P = ∑ j, a j := by
    rw [integral_finsetSum _ fun j _ => (hterm j).integrable one_le_two]
    simp [integral_mul_const, hmean]
  have hvarAnswer : variance (fun ω => ∑ j, mask j ω * a j) P = v * ∑ j, a j ^ 2 := by
    rw [hanswerFn, IndepFun.variance_sum (fun j _ => hterm j) fun i _ j _ hij =>
      (hindep hij).comp (measurable_id.mul_const (a i)) (measurable_id.mul_const (a j))]
    simp [variance_mul_const, hvar, Finset.mul_sum]
  have herror : MemLp (fun ω => y - ∑ j, mask j ω * a j) 2 P := (memLp_const y).sub hanswer
  have hmeanError : ∫ ω, y - ∑ j, mask j ω * a j ∂P = y - ∑ j, a j := by
    rw [integral_sub (integrable_const y) (hanswer.integrable one_le_two), hmeanAnswer]
    simp
  have hsplit := variance_eq_sub herror
  rw [variance_const_sub hanswer.aestronglyMeasurable y, hvarAnswer, hmeanError] at hsplit
  have hsquareFn : ∫ ω, (y - ∑ j, mask j ω * a j) ^ 2 ∂P
      = ∫ ω, ((fun ω => y - ∑ j, mask j ω * a j) ^ 2) ω ∂P := rfl
  rw [hsquareFn]
  linarith

variable {N : Type*} [Fintype N]

/-- **Over a set of examples.** Example `n` has features `x n` and label `y n`, the weights
are `θ`. The penalty on weight `j` is its square times the total squared size of feature
`j` over the examples. -/
theorem expected_dropout_loss_dataset {mask : ι → Ω → ℝ} (hsquare : ∀ j, MemLp (mask j) 2 P)
    (hindep : Pairwise fun i j => mask i ⟂ᵢ[P] mask j) (hmean : ∀ j, ∫ ω, mask j ω ∂P = 1)
    {v : ℝ} (hvar : ∀ j, variance (mask j) P = v) (y : N → ℝ) (x : N → ι → ℝ) (θ : ι → ℝ) :
    ∑ n, ∫ ω, (y n - ∑ j, mask j ω * (x n j * θ j)) ^ 2 ∂P
      = ∑ n, (y n - ∑ j, x n j * θ j) ^ 2 + v * ∑ j, (∑ n, x n j ^ 2) * θ j ^ 2 := by
  simp only [expected_dropout_loss P hsquare hindep hmean hvar, Finset.sum_add_distrib,
    ← Finset.mul_sum, mul_pow, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **Dropout is weight decay.** If every feature has the same total squared size `c`, the
penalty is `v c` times the squared length of the weights. -/
theorem expected_dropout_loss_of_equal_features {mask : ι → Ω → ℝ}
    (hsquare : ∀ j, MemLp (mask j) 2 P) (hindep : Pairwise fun i j => mask i ⟂ᵢ[P] mask j)
    (hmean : ∀ j, ∫ ω, mask j ω ∂P = 1) {v : ℝ} (hvar : ∀ j, variance (mask j) P = v)
    (y : N → ℝ) (x : N → ι → ℝ) (θ : ι → ℝ) {c : ℝ} (hequal : ∀ j, ∑ n, x n j ^ 2 = c) :
    ∑ n, ∫ ω, (y n - ∑ j, mask j ω * (x n j * θ j)) ^ 2 ∂P
      = ∑ n, (y n - ∑ j, x n j * θ j) ^ 2 + v * c * ∑ j, θ j ^ 2 := by
  rw [expected_dropout_loss_dataset P hsquare hindep hmean hvar]
  simp only [hequal, ← Finset.mul_sum, mul_assoc]

end Expectation

end SquigglyLine
