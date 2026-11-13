/-
How steep a network can be, and what that slope costs.

The theorem says a line is near the data only by being steep. These are the
places where the slope of a network shows up in practice.

Layers:
* `lipschitzWith_runLayers` : a stack of layers is no steeper than the
  product of the slopes of its layers.
* `lipschitzWith_activation_comp`, `lipschitzWith_relu` : a layer "weights,
  then ReLU" is no steeper than the size of its weights.
* `verticalDist_network_le` : so the slope sandwich reads in that product.
* `adjoint_comp_reverse`, `norm_adjoint_comp_le` : the gradient comes back
  through the layers in reverse and is bounded by the same product.

Adversarial examples:
* `le_mul_dist_of_flip` : to flip a classifier of slope `K` the input must
  move at least `score / K`.
* `score_add_sign`, `abs_score_add_sub_le` : for a linear model, nudging each
  input by `ε` in the worst direction moves the score by `ε` times the sum
  of the sizes of the weights, and no nudge of that size does more.

Temperature:
* `softmax_le_softmax_iff`, `softmax_temperature_order` : dividing the scores
  by a temperature never changes their order.

A critic of slope one:
* `sum_critic_gap_le` : the gap such a critic reports between paired points
  is at most the distance between them.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import SquigglyLine.Networks.MarkovChains
import SquigglyLine.Supporting.NetworkShape.SignedDistance
import SquigglyLine.Supporting.Training.CrossEntropy

namespace SquigglyLine

open NNReal

/-! ### Layers -/

section Layers

variable {α : Type*} [PseudoEMetricSpace α]

/-- **A network is no steeper than the product of its layers.** -/
theorem lipschitzWith_runLayers {layers : List (α → α)} {slopes : List ℝ≥0}
    (hlayers : List.Forall₂ (fun layer K => LipschitzWith K layer) layers slopes) :
    LipschitzWith slopes.prod (RUN_LAYERS layers) := by
  induction hlayers with
  | nil => simpa [RUN_LAYERS] using (LipschitzWith.id : LipschitzWith 1 (id : α → α))
  | cons hhead _ ih =>
    rw [RUN_LAYERS, List.prod_cons, mul_comm]
    exact ih.comp hhead

/-- A ReLU has slope at most one. -/
theorem lipschitzWith_relu : LipschitzWith 1 fun x : ℝ => max x 0 :=
  LipschitzWith.id.max_const 0

/-- A layer "weights `W`, then an activation of slope at most one" is no steeper than the
size of `W`. -/
theorem lipschitzWith_activation_comp {E F G : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] [SeminormedAddCommGroup F] [NormedSpace ℝ F] [PseudoEMetricSpace G]
    (W : E →L[ℝ] F) {σ : F → G} (hσ : LipschitzWith 1 σ) : LipschitzWith ‖W‖₊ (σ ∘ W) := by
  simpa using hσ.comp W.lipschitzWith

/-- **The sandwich for a network.** With a readout of slope `Kout` on top, the network can be
nearer to a data point than its vertical error only by the factor set by the product of the
slopes. -/
theorem verticalDist_network_le {X : Type*} [SeminormedAddCommGroup X] {layers : List (X → X)}
    {slopes : List ℝ≥0}
    (hlayers : List.Forall₂ (fun layer K => LipschitzWith K layer) layers slopes)
    {readout : X → ℝ} {Kout : ℝ≥0} (hout : LipschitzWith Kout readout) (p : DataPoint X) :
    GET_VERTICAL_ERROR (readout ∘ RUN_LAYERS layers) p
      ≤ √(1 + ((Kout * slopes.prod : ℝ≥0) : ℝ) ^ 2)
        * GET_NEAREST_DISTANCE (readout ∘ RUN_LAYERS layers) p :=
  verticalDist_le_of_lipschitz (hout.comp (lipschitzWith_runLayers hlayers)) p

end Layers

section Backward

open ContinuousLinearMap

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- **Backpropagation runs the layers in reverse.** The transpose of "first `B`, then `A`" is
"first the transpose of `A`, then the transpose of `B`". -/
theorem adjoint_comp_reverse (A : F →L[ℝ] G) (B : E →L[ℝ] F) :
    adjoint (A ∘L B) = adjoint B ∘L adjoint A :=
  adjoint_comp A B

omit [CompleteSpace F] in
/-- The gradient coming back is bounded by the same product of sizes as the signal going
forward. -/
theorem norm_adjoint_comp_le (A : F →L[ℝ] G) (B : E →L[ℝ] F) :
    ‖adjoint (A ∘L B)‖ ≤ ‖A‖ * ‖B‖ := by
  rw [LinearIsometryEquiv.norm_map]
  exact opNorm_comp_le A B

end Backward

/-! ### Adversarial examples -/

section Adversarial

/-- **Flipping a classifier takes a move of at least score over slope.** If the score at `x`
is positive and the score at `x'` is not, then `x'` is at least `score / K` away. -/
theorem le_mul_dist_of_flip {X : Type*} [PseudoMetricSpace X] {f : X → ℝ} {K : ℝ≥0}
    (hf : LipschitzWith K f) {x x' : X} (hflip : f x' ≤ 0) : f x ≤ K * dist x x' := by
  have hslope := hf.dist_le_mul x x'
  rw [Real.dist_eq] at hslope
  linarith [le_abs_self (f x - f x')]

variable {ι : Type*} [Fintype ι]

/-- The score of a linear model with weights `w` at the input `x`. -/
def GET_LINEAR_SCORE (w x : ι → ℝ) : ℝ :=
  ∑ i, w i * x i

/-- **The worst small nudge.** Move every input by `ε` in the direction of the sign of its
weight. The score moves by `ε` times the sum of the sizes of the weights. -/
theorem score_add_sign (w x : ι → ℝ) (ε : ℝ) :
    GET_LINEAR_SCORE w (fun i => x i + ε * SignType.sign (w i))
      = GET_LINEAR_SCORE w x + ε * ∑ i, |w i| := by
  simp only [GET_LINEAR_SCORE, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [← self_mul_sign (w i)]; ring

/-- No nudge of at most `ε` per input moves the score by more. -/
theorem abs_score_add_sub_le (w x δ : ι → ℝ) {ε : ℝ} (hδ : ∀ i, |δ i| ≤ ε) :
    |GET_LINEAR_SCORE w (fun i => x i + δ i) - GET_LINEAR_SCORE w x| ≤ ε * ∑ i, |w i| := by
  have hdiff : GET_LINEAR_SCORE w (fun i => x i + δ i) - GET_LINEAR_SCORE w x = ∑ i, w i * δ i := by
    simp only [GET_LINEAR_SCORE, mul_add, Finset.sum_add_distrib, add_sub_cancel_left]
  rw [hdiff, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hδ i) (abs_nonneg _)

end Adversarial

/-! ### Temperature -/

section Temperature

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- A larger score has a larger share. -/
theorem softmax_le_softmax_iff (z : ι → ℝ) (i j : ι) :
    APPLY_SOFTMAX z i ≤ APPLY_SOFTMAX z j ↔ z i ≤ z j := by
  rw [APPLY_SOFTMAX, APPLY_SOFTMAX, div_le_div_iff_of_pos_right (sum_exp_pos z), Real.exp_le_exp]

/-- **Temperature changes confidence, never the ranking.** -/
theorem softmax_temperature_order {T : ℝ} (hT : 0 < T) (z : ι → ℝ) (i j : ι) :
    APPLY_SOFTMAX (fun k => z k / T) i ≤ APPLY_SOFTMAX (fun k => z k / T) j
      ↔ APPLY_SOFTMAX z i ≤ APPLY_SOFTMAX z j := by
  rw [softmax_le_softmax_iff, softmax_le_softmax_iff, div_le_div_iff_of_pos_right hT]

end Temperature

/-! ### A critic of slope one -/

section Critic

variable {X ι : Type*} [PseudoMetricSpace X]

/-- **A critic of slope one cannot report more than the distance.** Pair each real sample with
a made one. The total gap in the critic's scores is at most the total distance between the
pairs. -/
theorem sum_critic_gap_le {critic : X → ℝ} (hcritic : LipschitzWith 1 critic) (s : Finset ι)
    (real made : ι → X) :
    ∑ i ∈ s, (critic (real i) - critic (made i)) ≤ ∑ i ∈ s, dist (real i) (made i) :=
  Finset.sum_le_sum fun i _ => by
    have hslope := hcritic.dist_le_mul (real i) (made i)
    rw [Real.dist_eq, NNReal.coe_one, one_mul] at hslope
    exact (le_abs_self _).trans hslope

end Critic

end SquigglyLine
