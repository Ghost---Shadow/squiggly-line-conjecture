/-
Averages: ensembles, weight averaging, and the ideal denoiser.

An average is never squigglier than what it averages, and never worse on
squared error than its members are on average.

Ensembles (`blend`):
* `sq_blend_sub` : the squared error of the average is the average squared
  error minus the spread of the members round the average.
* `sq_blend_sub_le` : so the average is at least as good as the members are
  on average.
* `lipschitzWith_blend` : and it is no steeper than the steepest member.

Weight averaging:
* `liftedModel_sum_smul` : for a model linear in its weights, averaging the
  weights is averaging the lines.
* `sq_liftedModel_soup_sub_le` : so the averaged weights are at least as good
  as the members are on average.

The ideal denoiser (`idealDenoiser`):
* `sum_mul_norm_sub_sq` : the weighted squared distance to any point is the
  weighted squared distance to the weighted mean plus the squared distance
  from the mean to the point.
* `weightedMean_isBest` : so the weighted mean is the best single guess.
* `idealDenoiser_isBest` : the ideal denoiser is that mean, with shares set
  by nearness to the noisy input. It is an attention head over the training
  examples.
* `idealDenoiser_mem_convexHull` : so it never leaves the region the training
  examples span.
-/
import SquigglyLine.Networks.Lift
import SquigglyLine.Supporting.NetworkShape.Attention

namespace SquigglyLine

open NNReal

/-! ### Ensembles -/

section Ensemble

variable {ι : Type*} (s : Finset ι) (w f : ι → ℝ)

/-- The average of the predictions `f` with shares `w`. -/
def blend : ℝ :=
  ∑ i ∈ s, w i * f i

theorem sum_mul_sq_sub (c : ℝ) :
    ∑ i ∈ s, w i * (f i - c) ^ 2
      = ∑ i ∈ s, w i * f i ^ 2 - 2 * c * ∑ i ∈ s, w i * f i + c ^ 2 * ∑ i ∈ s, w i := by
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The error of the average is the average error minus the spread.** -/
theorem sq_blend_sub (hw : ∑ i ∈ s, w i = 1) (y : ℝ) :
    (blend s w f - y) ^ 2
      = ∑ i ∈ s, w i * (f i - y) ^ 2 - ∑ i ∈ s, w i * (f i - blend s w f) ^ 2 := by
  rw [sum_mul_sq_sub, sum_mul_sq_sub, hw]
  simp only [blend]
  ring

/-- **An ensemble is at least as good as its members are on average.** -/
theorem sq_blend_sub_le (hnonneg : ∀ i ∈ s, 0 ≤ w i) (hw : ∑ i ∈ s, w i = 1) (y : ℝ) :
    (blend s w f - y) ^ 2 ≤ ∑ i ∈ s, w i * (f i - y) ^ 2 := by
  have hspread : 0 ≤ ∑ i ∈ s, w i * (f i - blend s w f) ^ 2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hnonneg i hi) (sq_nonneg _)
  rw [sq_blend_sub s w f hw]
  linarith

/-- **An average is no steeper than its steepest member.** -/
theorem lipschitzWith_blend {X : Type*} [PseudoMetricSpace X] {K : ℝ≥0} {lines : ι → X → ℝ}
    (hlines : ∀ i ∈ s, LipschitzWith K (lines i)) (hnonneg : ∀ i ∈ s, 0 ≤ w i)
    (hw : ∑ i ∈ s, w i = 1) : LipschitzWith K fun x => ∑ i ∈ s, w i * lines i x := by
  refine LipschitzWith.of_dist_le_mul fun x x' => ?_
  rw [Real.dist_eq, ← Finset.sum_sub_distrib]
  calc |∑ i ∈ s, (w i * lines i x - w i * lines i x')|
      ≤ ∑ i ∈ s, |w i * lines i x - w i * lines i x'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, w i * (K * dist x x') := Finset.sum_le_sum fun i hi => by
        have hslope := (hlines i hi).dist_le_mul x x'
        rw [Real.dist_eq] at hslope
        rw [← mul_sub, abs_mul, abs_of_nonneg (hnonneg i hi)]
        exact mul_le_mul_of_nonneg_left hslope (hnonneg i hi)
    _ = K * dist x x' := by rw [← Finset.sum_mul, hw, one_mul]

end Ensemble

/-! ### Weight averaging -/

section Soup

variable {X Θ ι : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]

/-- **Averaging weights is averaging lines**, for a model linear in its weights. -/
theorem liftedModel_sum_smul (φ : X → Θ) (s : Finset ι) (w : ι → ℝ) (θ : ι → Θ) (x : X) :
    liftedModel φ (∑ i ∈ s, w i • θ i) x = ∑ i ∈ s, w i * liftedModel φ (θ i) x := by
  simp only [liftedModel, sum_inner, inner_smul_left]
  rfl

/-- **Averaged weights are at least as good as the members are on average.** -/
theorem sq_liftedModel_soup_sub_le (φ : X → Θ) (s : Finset ι) {w : ι → ℝ} (θ : ι → Θ)
    (hnonneg : ∀ i ∈ s, 0 ≤ w i) (hw : ∑ i ∈ s, w i = 1) (x : X) (y : ℝ) :
    (liftedModel φ (∑ i ∈ s, w i • θ i) x - y) ^ 2
      ≤ ∑ i ∈ s, w i * (liftedModel φ (θ i) x - y) ^ 2 := by
  rw [liftedModel_sum_smul]
  exact sq_blend_sub_le s w (fun i => liftedModel φ (θ i) x) hnonneg hw y

end Soup

/-! ### The ideal denoiser -/

section Denoiser

variable {ι V : Type*} [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The mean of the points `x` with shares `p`. -/
def weightedMean (p : ι → ℝ) (x : ι → V) : V :=
  ∑ i, p i • x i

theorem sum_smul_sub_weightedMean {p : ι → ℝ} (hp : ∑ i, p i = 1) (x : ι → V) :
    ∑ i, p i • (x i - weightedMean p x) = 0 := by
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hp, one_smul]
  exact sub_self _

/-- The weighted squared distance to any point `c` splits into the weighted squared distance
to the mean, plus the squared distance from the mean to `c`. -/
theorem sum_mul_norm_sub_sq {p : ι → ℝ} (hp : ∑ i, p i = 1) (x : ι → V) (c : V) :
    ∑ i, p i * ‖x i - c‖ ^ 2
      = ∑ i, p i * ‖x i - weightedMean p x‖ ^ 2 + ‖weightedMean p x - c‖ ^ 2 := by
  have hcross : ∑ i, p i * inner ℝ (x i - weightedMean p x) (weightedMean p x - c) = 0 := by
    simp only [← real_inner_smul_left, ← sum_inner, sum_smul_sub_weightedMean hp, inner_zero_left]
  have hterm (i : ι) : p i * ‖x i - c‖ ^ 2
      = p i * ‖x i - weightedMean p x‖ ^ 2
        + 2 * (p i * inner ℝ (x i - weightedMean p x) (weightedMean p x - c))
        + p i * ‖weightedMean p x - c‖ ^ 2 := by
    rw [show x i - c = x i - weightedMean p x + (weightedMean p x - c) by abel,
      norm_add_sq_real]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hcross, ← Finset.sum_mul, hp]
  ring

/-- **The weighted mean is the best single guess.** -/
theorem weightedMean_isBest {p : ι → ℝ} (hp : ∑ i, p i = 1) (x : ι → V) (c : V) :
    ∑ i, p i * ‖x i - weightedMean p x‖ ^ 2 ≤ ∑ i, p i * ‖x i - c‖ ^ 2 := by
  rw [sum_mul_norm_sub_sq hp x c]
  exact le_add_of_nonneg_right (sq_nonneg _)

variable [Nonempty ι]

/-- The ideal denoiser for the training examples `x` at noise level `σ`. Given a noisy input
`y`, each example gets a share that falls with its squared distance from `y`, and the output
is the examples averaged with those shares. -/
noncomputable def idealDenoiser (σ : ℝ) (x : ι → V) (y : V) : V :=
  attend (fun i => -‖y - x i‖ ^ 2 / (2 * σ ^ 2)) x

omit [Nonempty ι] in
/-- The ideal denoiser is the mean of the examples with softmax shares. -/
theorem idealDenoiser_eq_weightedMean (σ : ℝ) (x : ι → V) (y : V) :
    idealDenoiser σ x y = weightedMean (softmax fun i => -‖y - x i‖ ^ 2 / (2 * σ ^ 2)) x :=
  rfl

/-- **No other guess is better.** Among all outputs `c`, the ideal denoiser has the least
squared distance to the examples, weighted by how likely each is to be the clean one. -/
theorem idealDenoiser_isBest (σ : ℝ) (x : ι → V) (y c : V) :
    ∑ i, softmax (fun j => -‖y - x j‖ ^ 2 / (2 * σ ^ 2)) i * ‖x i - idealDenoiser σ x y‖ ^ 2
      ≤ ∑ i, softmax (fun j => -‖y - x j‖ ^ 2 / (2 * σ ^ 2)) i * ‖x i - c‖ ^ 2 :=
  weightedMean_isBest (sum_softmax _) x c

/-- **The ideal denoiser only averages its training set.** Its output never leaves the region
the training examples span. -/
theorem idealDenoiser_mem_convexHull (σ : ℝ) (x : ι → V) (y : V) :
    idealDenoiser σ x y ∈ convexHull ℝ (Set.range x) :=
  attend_mem_convexHull _ x

end Denoiser

end SquigglyLine
