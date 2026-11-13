/-
Nearest neighbours, k-means and contrastive learning: three uses of nearness.

* **Nearest neighbours.** Copying the label of the nearest training input is
  wrong by at most the slope of the truth times the distance to that input.
* **k-means.** Each half of a step lowers the cost or leaves it: moving every
  point to its nearest centre, and moving every centre to the mean of its
  points.
* **Contrastive learning.** For vectors of length one, the dot product is one
  minus half the squared distance. So a softmax over cosine similarity at
  temperature `τ` is a softmax over squared distance: the same weights as the
  ideal denoiser of `Averaging.lean` with noise level `√τ`.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Theorems: `abs_sub_nearest_le`, `sum_sq_reassign_le`, `sum_sq_mean_le`,
`softmax_add_const`, `inner_eq_one_sub_of_unit`,
`softmax_cosine_eq_softmax_distance`.
-/
import SquigglyLine.Supporting.NewInputs.Averaging

namespace SquigglyLine

open Real NNReal

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- **Nearest neighbours.** If the truth `f` has slope at most `K`, then copying the label of
the nearest training input `x i` is wrong by at most `K` times the distance from the query to
any training input, and so to the nearest. -/
theorem abs_sub_nearest_le {f : E → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f) (q : E) (x : ι → E)
    {i : ι} (hi : ∀ j, dist q (x i) ≤ dist q (x j)) (j : ι) :
    |f q - f (x i)| ≤ K * dist q (x j) := by
  have h := hf.dist_le_mul q (x i)
  rw [Real.dist_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hi j) K.coe_nonneg)

variable {κ : Type*} [Fintype ι]

omit [InnerProductSpace ℝ E] in
/-- **k-means, first half.** Give every point a centre that is no further than the one it
had. The cost does not rise. -/
theorem sum_sq_reassign_le (x : ι → E) (c : κ → E) (old new : ι → κ)
    (h : ∀ i, ‖x i - c (new i)‖ ≤ ‖x i - c (old i)‖) :
    ∑ i, ‖x i - c (new i)‖ ^ 2 ≤ ∑ i, ‖x i - c (old i)‖ ^ 2 :=
  Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2

/-- **k-means, second half.** For the points of one cluster, no centre has a lower cost than
their mean. -/
theorem sum_sq_mean_le [Nonempty ι] (x : ι → E) (c : E) :
    ∑ i, ‖x i - GET_WEIGHTED_MEAN (fun _ => (Fintype.card ι : ℝ)⁻¹) x‖ ^ 2
      ≤ ∑ i, ‖x i - c‖ ^ 2 := by
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ _i : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hcard.ne']
  have h : ∑ i, (Fintype.card ι : ℝ)⁻¹
        * ‖x i - GET_WEIGHTED_MEAN (fun _ => (Fintype.card ι : ℝ)⁻¹) x‖ ^ 2
      ≤ ∑ i, (Fintype.card ι : ℝ)⁻¹ * ‖x i - c‖ ^ 2 :=
    weightedMean_isBest hsum x c
  simp only [← Finset.mul_sum] at h
  exact le_of_mul_le_mul_left h (inv_pos.mpr hcard)

/-- Adding the same number to every score changes no share of the softmax. -/
theorem softmax_add_const (z : ι → ℝ) (c : ℝ) :
    APPLY_SOFTMAX (fun i => z i + c) = APPLY_SOFTMAX z := by
  funext i
  simp only [APPLY_SOFTMAX, exp_add, ← Finset.sum_mul]
  rw [mul_div_mul_right _ _ (exp_pos c).ne']

/-- For two vectors of length one, the dot product is one minus half the squared distance. -/
theorem inner_eq_one_sub_of_unit {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    inner ℝ u v = 1 - ‖u - v‖ ^ 2 / 2 := by
  have h := norm_sub_sq_real u v
  rw [hu, hv] at h
  linarith

/-- **Contrastive learning scores by nearness.** For vectors of length one, the softmax over
cosine similarity at temperature `τ` is the softmax over minus the squared distance, divided
by `2 τ`. -/
theorem softmax_cosine_eq_softmax_distance {q : E} {k : ι → E} (hq : ‖q‖ = 1)
    (hk : ∀ i, ‖k i‖ = 1) (τ : ℝ) :
    APPLY_SOFTMAX (fun i => inner ℝ q (k i) / τ)
      = APPLY_SOFTMAX fun i => -‖q - k i‖ ^ 2 / (2 * τ) := by
  have h : (fun i => inner ℝ q (k i) / τ) = fun i => -‖q - k i‖ ^ 2 / (2 * τ) + 1 / τ := by
    funext i
    rw [inner_eq_one_sub_of_unit hq (hk i)]
    ring
  rw [h, softmax_add_const]

end SquigglyLine
