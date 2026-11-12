/-
A gain per step: where it should be one, and where it should be below one.

`VanishingGradients.lean` shows that a gain `g` per layer becomes `g ^ L`
after `L` layers. Two well-known designs are choices of that gain.

He initialisation, which sets the gain of a fold to one:
* `relu_sq_add_relu_neg_sq` : a fold keeps the squared size of the positive
  part and drops the rest: the two parts add up to the whole.
* `integral_relu_sq_of_symmetric` : so for a signal that is as often negative
  as positive, a fold keeps exactly half the mean squared size.
* `he_gain` : `n` inputs with weights of variance `2 / n` make up for the half.

The Bellman update of reinforcement learning, whose gain is below one:
* `lipschitzWith_bellman` : one sweep of value updates has slope at most the
  discount `γ`.
* `dist_iterate_bellman_le` : so after `n` sweeps any two guesses are within
  `γ ^ n` of their starting distance.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Pseudo.Pi

namespace SquigglyLine

open MeasureTheory NNReal

/-! ### He initialisation -/

section He

/-- **A fold splits the squared size in two.** The part a ReLU keeps and the part it would
have kept of the mirror image add up to the whole. -/
theorem relu_sq_add_relu_neg_sq (x : ℝ) : max x 0 ^ 2 + max (-x) 0 ^ 2 = x ^ 2 := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h)]
    ring

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)

/-- **A fold keeps half.** If a signal is as often negative as positive, in the sense that its
mirror image has the same mean squared size after the fold, then the fold keeps exactly half
of the mean squared size. -/
theorem integral_relu_sq_of_symmetric {X : Ω → ℝ}
    (hpos : Integrable (fun ω => max (X ω) 0 ^ 2) P)
    (hneg : Integrable (fun ω => max (-X ω) 0 ^ 2) P)
    (hsym : ∫ ω, max (-X ω) 0 ^ 2 ∂P = ∫ ω, max (X ω) 0 ^ 2 ∂P) :
    ∫ ω, max (X ω) 0 ^ 2 ∂P = (∫ ω, X ω ^ 2 ∂P) / 2 := by
  have hsum : ∫ ω, X ω ^ 2 ∂P
      = ∫ ω, max (X ω) 0 ^ 2 ∂P + ∫ ω, max (-X ω) 0 ^ 2 ∂P := by
    rw [← integral_add hpos hneg]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    exact (relu_sq_add_relu_neg_sq (X ω)).symm
  rw [hsum, hsym]
  ring

/-- **The factor two of He initialisation.** A unit adds up `n` inputs. With weights of
variance `2 / n`, the half lost in the fold is made up exactly, and the gain is one. -/
theorem he_gain {n : ℝ} (hn : n ≠ 0) : n * (2 / n) * (1 / 2) = 1 := by
  field_simp

end He

/-! ### The Bellman update -/

section Bellman

variable {S : Type*} [Fintype S]

/-- One sweep of value updates. `r s` is the reward in state `s`, `P s s'` the chance of
moving from `s` to `s'`, and `γ` the discount. -/
def bellman (r : S → ℝ) (P : S → S → ℝ) (γ : ℝ) (V : S → ℝ) : S → ℝ :=
  fun s => r s + γ * ∑ s', P s s' * V s'

variable {P : S → S → ℝ}

/-- **A sweep has slope at most the discount.** Two guesses at the values are brought closer
by the factor `γ`, measured by their largest disagreement. -/
theorem lipschitzWith_bellman (hP : ∀ s s', 0 ≤ P s s') (hrow : ∀ s, ∑ s', P s s' = 1)
    (γ : ℝ≥0) (r : S → ℝ) : LipschitzWith γ (bellman r P γ) := by
  refine LipschitzWith.of_dist_le_mul fun V V' => ?_
  refine (dist_pi_le_iff (by positivity)).2 fun s => ?_
  have hdiff : bellman r P γ V s - bellman r P γ V' s
      = γ * ∑ s', P s s' * (V s' - V' s') := by
    simp only [bellman, mul_sub, Finset.sum_sub_distrib]
    ring
  rw [Real.dist_eq, hdiff, abs_mul, abs_of_nonneg γ.coe_nonneg]
  refine mul_le_mul_of_nonneg_left ?_ γ.coe_nonneg
  calc |∑ s', P s s' * (V s' - V' s')|
      ≤ ∑ s', |P s s' * (V s' - V' s')| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', P s s' * dist V V' := Finset.sum_le_sum fun s' _ => by
        have hstate := dist_le_pi_dist V V' s'
        rw [Real.dist_eq] at hstate
        rw [abs_mul, abs_of_nonneg (hP s s')]
        exact mul_le_mul_of_nonneg_left hstate (hP s s')
    _ = dist V V' := by rw [← Finset.sum_mul, hrow, one_mul]

/-- **Repeated sweeps pull every guess to one answer.** After `n` sweeps, two guesses differ
by at most `γ ^ n` times what they differed by at the start. -/
theorem dist_iterate_bellman_le (hP : ∀ s s', 0 ≤ P s s') (hrow : ∀ s, ∑ s', P s s' = 1)
    (γ : ℝ≥0) (r : S → ℝ) (n : ℕ) (V V' : S → ℝ) :
    dist ((bellman r P γ)^[n] V) ((bellman r P γ)^[n] V') ≤ (γ : ℝ) ^ n * dist V V' := by
  simpa using ((lipschitzWith_bellman hP hrow γ r).iterate n).dist_le_mul V V'

end Bellman

end SquigglyLine
