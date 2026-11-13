/-
Hard choices: the straight-through trick, a cold softmax, and Hopfield recall.

* **Straight-through.** A hard step, such as rounding, has slope zero where
  it is not jumping, so no gradient comes back through it. The trick
  `(hard - soft).detach() + soft` has the value of the hard step and the
  slope of the gentle stand-in.
* **A cold softmax picks.** At temperature `τ` the share of the top score is
  within `(n - 1) * exp (-gap / τ)` of one, where `gap` is its lead over the
  rest. This is the gentle stand-in of Gumbel-softmax, and it tends to the
  pick itself as `τ` falls.
* **Hopfield recall.** The update of a modern Hopfield network is an
  attention head over the stored patterns. For patterns and a query of
  length one it is the ideal denoiser of `Averaging.lean`.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Definitions: `APPLY_STRAIGHT_THROUGH`.

Theorems: `hasDerivAt_step_of_pos`, `straightThrough_self`,
`hasDerivAt_straightThrough`, `one_sub_softmax_div_le`,
`hopfield_eq_denoiser`.
-/
import SquigglyLine.Supporting.NewInputs.Neighbours

namespace SquigglyLine

open Real

/-- **A hard step sends no gradient back.** Away from its jump, the step function has slope
zero. -/
theorem hasDerivAt_step_of_pos {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x : ℝ => if 0 ≤ x then (1 : ℝ) else 0) 0 t := by
  have h : (fun x : ℝ => if 0 ≤ x then (1 : ℝ) else 0) =ᶠ[nhds t] fun _ => 1 := by
    filter_upwards [eventually_gt_nhds ht] with x hx
    simp [hx.le]
  exact (hasDerivAt_const t (1 : ℝ)).congr_of_eventuallyEq h

/-- The straight-through trick at the point `t₀`: the hard value there, with the gentle
stand-in carrying the dependence on the input.
Python: `(hard(t) - soft(t)).detach() + soft(t)`. -/
def APPLY_STRAIGHT_THROUGH (hard soft : ℝ → ℝ) (t₀ : ℝ) : ℝ → ℝ :=
  fun t => hard t₀ - soft t₀ + soft t

/-- **Forward, it is the hard step.** -/
theorem straightThrough_self (hard soft : ℝ → ℝ) (t₀ : ℝ) :
    APPLY_STRAIGHT_THROUGH hard soft t₀ t₀ = hard t₀ := by
  simp [APPLY_STRAIGHT_THROUGH]

/-- **Backward, it has the slope of the stand-in.** -/
theorem hasDerivAt_straightThrough (hard : ℝ → ℝ) {soft : ℝ → ℝ} {s t₀ : ℝ}
    (h : HasDerivAt soft s t₀) :
    HasDerivAt (APPLY_STRAIGHT_THROUGH hard soft t₀) s t₀ :=
  h.const_add (hard t₀ - soft t₀)

variable {ι : Type*} [Fintype ι]

/-- **A cold softmax picks the top score.** If score `i` leads every other by at least `gap`,
then at temperature `τ` its share is within `(n - 1) * exp (-gap / τ)` of one. -/
theorem one_sub_softmax_div_le [DecidableEq ι] [Nonempty ι] {z : ι → ℝ} {i : ι} {gap τ : ℝ}
    (hτ : 0 < τ) (hgap : ∀ j, j ≠ i → z j + gap ≤ z i) :
    1 - APPLY_SOFTMAX (fun j => z j / τ) i ≤ (Fintype.card ι - 1) * exp (-gap / τ) := by
  have hsum : ∑ j, APPLY_SOFTMAX (fun j => z j / τ) j = 1 := sum_softmax _
  have hsplit : 1 - APPLY_SOFTMAX (fun j => z j / τ) i
      = ∑ j ∈ Finset.univ.erase i, APPLY_SOFTMAX (fun j => z j / τ) j := by
    rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    ring
  have hS : exp (z i / τ) ≤ ∑ k, exp (z k / τ) :=
    Finset.single_le_sum (f := fun k => exp (z k / τ)) (fun k _ => (exp_pos _).le)
      (Finset.mem_univ i)
  have hterm : ∀ j ∈ Finset.univ.erase i,
      APPLY_SOFTMAX (fun j => z j / τ) j ≤ exp (-gap / τ) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    calc APPLY_SOFTMAX (fun j => z j / τ) j
        = exp (z j / τ) / ∑ k, exp (z k / τ) := rfl
      _ ≤ exp (z j / τ) / exp (z i / τ) :=
          div_le_div_of_nonneg_left (exp_pos _).le (exp_pos _) hS
      _ = exp (z j / τ - z i / τ) := by rw [exp_sub]
      _ ≤ exp (-gap / τ) := by
          refine exp_le_exp.mpr ?_
          rw [← sub_div]
          exact div_le_div_of_nonneg_right (by linarith [hgap j hji]) hτ.le
  have hcard : ((Finset.univ.erase i).card : ℝ) = Fintype.card ι - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Nat.cast_sub Fintype.card_pos]
    simp
  calc 1 - APPLY_SOFTMAX (fun j => z j / τ) i
      = ∑ j ∈ Finset.univ.erase i, APPLY_SOFTMAX (fun j => z j / τ) j := hsplit
    _ ≤ ∑ _j ∈ Finset.univ.erase i, exp (-gap / τ) := Finset.sum_le_sum hterm
    _ = (Fintype.card ι - 1) * exp (-gap / τ) := by
        rw [Finset.sum_const, nsmul_eq_mul, hcard]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Nonempty ι]

omit [Nonempty ι] in
/-- **Hopfield recall is the ideal denoiser.** A modern Hopfield network updates its state to
an attention-weighted average of the stored patterns, scored by overlap with the state. For
patterns and a state of length one, that is the ideal denoiser at noise level `√τ`. -/
theorem hopfield_eq_denoiser {q : E} {k : ι → E} (hq : ‖q‖ = 1) (hk : ∀ i, ‖k i‖ = 1)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ATTEND (fun i => inner ℝ q (k i) / τ) k = DENOISE_IDEALLY (√τ) k q := by
  rw [DENOISE_IDEALLY, ATTEND, ATTEND, Real.sq_sqrt hτ,
    softmax_cosine_eq_softmax_distance hq hk τ]

end SquigglyLine
