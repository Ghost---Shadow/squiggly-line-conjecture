/-
Counting: why a count is hard for a model made of averages and slopes.

A count is a step: it is a whole number, and it jumps. Four facts say why
that is the worst kind of function for the models in this project.

* A read-out that changes smoothly from `k` to `k + 1` says `k + 1/2`
  somewhere on the way.
* An attention head that scores two examples equally returns the point half
  way between them, and so does the ideal denoiser at a noisy input equally
  far from two training examples.
* A model that says `k` at one input and `k + 1` at another has slope at
  least one over their distance.

The fourth fact, that a stack of local layers cannot see the whole input, is
`iterate_convolution_congr` in `Convolution.lean`.

These show that counting is hard for such models. They do not show that
this is why a real image model draws the wrong number of fingers.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Theorems: `exists_half_count`, `attend_two_of_const_score`,
`denoiser_two_of_equidistant`, `one_le_slope_mul_dist_of_count`.
-/
import Mathlib.Topology.Order.IntermediateValue
import SquigglyLine.Supporting.NewInputs.Averaging

namespace SquigglyLine

open NNReal

/-- **Between two counts there is a half.** A read-out that is continuous along a path, and
says `k` at one end and `k + 1` at the other, says `k + 1/2` somewhere on the path. -/
theorem exists_half_count {r : ℝ → ℝ} {k : ℝ} (hr : ContinuousOn r (Set.Icc 0 1))
    (h0 : r 0 = k) (h1 : r 1 = k + 1) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, r t = k + 1 / 2 := by
  have hmem : k + 1 / 2 ∈ Set.Icc (r 0) (r 1) := by
    rw [h0, h1]
    constructor <;> linarith
  obtain ⟨t, ht, hrt⟩ := intermediate_value_Icc zero_le_one hr hmem
  exact ⟨t, ht, hrt⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- An attention head that scores two examples equally returns the point half way between
them. -/
theorem attend_two_of_const_score (c : ℝ) (v : Fin 2 → E) :
    ATTEND (fun _ : Fin 2 => c) v = (1 / 2 : ℝ) • (v 0 + v 1) := by
  have h : ATTEND (fun _ : Fin 2 => c) v = (Fintype.card (Fin 2) : ℝ)⁻¹ • ∑ i, v i :=
    attend_of_const_score c v
  rw [h, Fin.sum_univ_two, Fintype.card_fin]
  norm_num

/-- **The ideal denoiser blends counts.** At a noisy input equally far from two training
examples, it returns the point half way between them: half of one hand and half of the
other. -/
theorem denoiser_two_of_equidistant (σ : ℝ) (x : Fin 2 → E) {y : E}
    (h : ‖y - x 1‖ = ‖y - x 0‖) :
    DENOISE_IDEALLY σ x y = (1 / 2 : ℝ) • (x 0 + x 1) := by
  have hall : ∀ i : Fin 2, ‖y - x i‖ = ‖y - x 0‖ := Fin.forall_fin_two.mpr ⟨rfl, h⟩
  have hs : (fun i : Fin 2 => -‖y - x i‖ ^ 2 / (2 * σ ^ 2))
      = fun _ => -‖y - x 0‖ ^ 2 / (2 * σ ^ 2) := by
    funext i
    rw [hall i]
  rw [DENOISE_IDEALLY, hs]
  exact attend_two_of_const_score _ x

/-- **Being sharp about a count costs slope.** A model that says `k` at one input and
`k + 1` at another has slope at least one over the distance between them. -/
theorem one_le_slope_mul_dist_of_count {X : Type*} [PseudoMetricSpace X] {f : X → ℝ}
    {K : ℝ≥0} (hf : LipschitzWith K f) {x x' : X} {k : ℝ} (hx : f x = k)
    (hx' : f x' = k + 1) :
    1 ≤ K * dist x x' := by
  have h := hf.dist_le_mul x x'
  rw [Real.dist_eq, hx, hx'] at h
  have habs : |k - (k + 1)| = 1 := by
    rw [show k - (k + 1) = -1 by ring]
    simp
  linarith

end SquigglyLine
