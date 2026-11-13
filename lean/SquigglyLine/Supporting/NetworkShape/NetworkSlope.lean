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
* `le_mul_dist_of_flip` : to flip a classifier of slope `slope_limit` the
  input must move at least `score / slope_limit`.
* `GET_LINEAR_SCORE` : the score of a linear model.
* `score_add_sign`, `abs_score_add_sub_le` : for a linear model, nudging each
  input by `nudge` in the worst direction moves the score by `nudge` times the
  sum of the sizes of the weights, and no nudge of that size does more.

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

variable {State : Type*} [PseudoEMetricSpace State]

/-- **A network is no steeper than the product of its layers.** -/
theorem lipschitzWith_runLayers
    {layers : LayerStack State}
    {slopes : List SlopeLimit}
    (each_layer_has_its_slope :
      List.Forall₂ (fun layer slope => LipschitzWith slope layer)
        layers slopes) :
    let network       := RUN_LAYERS layers
    let slope_product := slopes.prod  -- slopes multiply when functions are composed
    LipschitzWith slope_product network := by
  unfold_named_pieces
  induction each_layer_has_its_slope with
  | nil =>
    simpa [RUN_LAYERS] using (LipschitzWith.id : LipschitzWith 1 (id : State → State))
  | cons head_has_its_slope _ ih =>
    rw [RUN_LAYERS, List.prod_cons, mul_comm]
    exact ih.comp head_has_its_slope

/-- A ReLU has slope at most one. -/
theorem lipschitzWith_relu :
    let slope_limit : SlopeLimit := 1
    LipschitzWith slope_limit fun input : ℝ => max input 0 := by
  unfold_named_pieces
  exact LipschitzWith.id.max_const 0

/-- A layer "weights, then an activation of slope at most one" is no steeper
than the size of the weights. -/
theorem lipschitzWith_activation_comp
    {Inputs Hidden Outputs : Type*}
    [SeminormedAddCommGroup Inputs] [NormedSpace ℝ Inputs]
    [SeminormedAddCommGroup Hidden] [NormedSpace ℝ Hidden]
    [PseudoEMetricSpace Outputs]
    (weights : Inputs →L[ℝ] Hidden)
    {activation : Hidden → Outputs}
    (activation_has_slope_one : LipschitzWith 1 activation) :
    let layer : Inputs → Outputs := activation ∘ weights
    let weights_size             := ‖weights‖₊
    LipschitzWith weights_size layer := by
  unfold_named_pieces
  simpa using activation_has_slope_one.comp weights.lipschitzWith

/-- **The sandwich for a network.** With a readout of slope `readout_slope` on
top, the network can be nearer to a data point than its vertical error only by
the factor set by the product of the slopes. -/
theorem verticalDist_network_le
    {Features : Type*} [SeminormedAddCommGroup Features]
    {layers : LayerStack Features}
    {slopes : List SlopeLimit}
    (each_layer_has_its_slope :
      List.Forall₂ (fun layer slope => LipschitzWith slope layer)
        layers slopes)
    {readout : Features → ℝ}
    {readout_slope : SlopeLimit}
    (readout_is_bounded : LipschitzWith readout_slope readout)
    (data_point : DataPoint Features) :
    let network : Model Features := readout ∘ RUN_LAYERS layers
    let vertical_error   := GET_VERTICAL_ERROR network data_point
    let nearest_distance := GET_NEAREST_DISTANCE network data_point
    let total_slope : ℝ  := ((readout_slope * slopes.prod : SlopeLimit) : ℝ)
    let stretch          := √(1 + total_slope ^ 2)  -- Pythagoras: 1 across, total_slope up
    vertical_error ≤ stretch * nearest_distance := by
  unfold_named_pieces
  exact verticalDist_le_of_lipschitz
    (readout_is_bounded.comp (lipschitzWith_runLayers each_layer_has_its_slope))
    data_point

end Layers

section Backward

open ContinuousLinearMap

variable {Source Middle Target : Type*}
  [NormedAddCommGroup Source] [InnerProductSpace ℝ Source] [CompleteSpace Source]
  [NormedAddCommGroup Middle] [InnerProductSpace ℝ Middle] [CompleteSpace Middle]
  [NormedAddCommGroup Target] [InnerProductSpace ℝ Target] [CompleteSpace Target]

/-- **Backpropagation runs the layers in reverse.** The transpose of "first
`first_map`, then `second_map`" is "first the transpose of `second_map`, then
the transpose of `first_map`". -/
theorem adjoint_comp_reverse
    (second_map : Middle →L[ℝ] Target)
    (first_map : Source →L[ℝ] Middle) :
    let transpose_of_both    := adjoint (second_map ∘L first_map)
    let transpose_in_reverse := adjoint first_map ∘L adjoint second_map
    transpose_of_both = transpose_in_reverse := by
  unfold_named_pieces
  exact adjoint_comp second_map first_map

omit [CompleteSpace Middle] in
/-- The gradient coming back is bounded by the same product of sizes as the
signal going forward. -/
theorem norm_adjoint_comp_le
    (second_map : Middle →L[ℝ] Target)
    (first_map : Source →L[ℝ] Middle) :
    let size_of_transpose := ‖adjoint (second_map ∘L first_map)‖
    let product_of_sizes  := ‖second_map‖ * ‖first_map‖
    size_of_transpose ≤ product_of_sizes := by
  unfold_named_pieces
  rw [LinearIsometryEquiv.norm_map]
  exact opNorm_comp_le second_map first_map

end Backward

/-! ### Adversarial examples -/

section Adversarial

/-- **Flipping a classifier takes a move of at least score over slope.** If the
score at `input` is positive and the score at `other_input` is not, then
`other_input` is at least `score / slope_limit` away. -/
theorem le_mul_dist_of_flip
    {Inputs : Type*} [PseudoMetricSpace Inputs]
    {model : Inputs → ℝ}
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit model)
    {input other_input : Inputs}
    (score_has_flipped : model other_input ≤ 0) :
    let score         := model input
    let allowed_score : ℝ := slope_limit * dist input other_input  -- the score cannot change faster than the slope
    score ≤ allowed_score := by
  unfold_named_pieces
  have score_change := slope_is_bounded.dist_le_mul input other_input
  rw [Real.dist_eq] at score_change
  linarith [le_abs_self (model input - model other_input)]

variable {Coordinates : Type*} [Fintype Coordinates]

/-- The score of a linear model with the given weights at the given input.
Python: `sum(w * x for w, x in zip(weights, input))`. -/
def GET_LINEAR_SCORE
    (weights : Coordinates → ℝ)
    (input : Coordinates → ℝ) : ℝ :=
  ∑ i, weights i * input i

/-- **The worst small nudge.** Move every input by `nudge_size` in the direction
of the sign of its weight. The score moves by `nudge_size` times the sum of the
sizes of the weights. -/
theorem score_add_sign
    (weights : Coordinates → ℝ)
    (input : Coordinates → ℝ)
    (nudge_size : ℝ) :
    let nudged_input : Coordinates → ℝ :=
      fun i => input i + nudge_size * SignType.sign (weights i)
    let score_before        := GET_LINEAR_SCORE weights input
    let total_weight_size   := ∑ i, |weights i|
    let score_after         := GET_LINEAR_SCORE weights nudged_input
    let predicted_score     := score_before + nudge_size * total_weight_size
    score_after = predicted_score := by
  unfold_named_pieces
  simp only [GET_LINEAR_SCORE, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  -- Each term is `|weight|` times the nudge, since `weight * sign weight = |weight|`.
  exact Finset.sum_congr rfl fun i _ => by rw [← self_mul_sign (weights i)]; ring

/-- No nudge of at most `size_limit` per input moves the score by more. -/
theorem abs_score_add_sub_le
    (weights : Coordinates → ℝ)
    (input : Coordinates → ℝ)
    (nudge : Coordinates → ℝ)
    {size_limit : ℝ}
    (nudge_is_small : ∀ i, |nudge i| ≤ size_limit) :
    let nudged_input : Coordinates → ℝ := fun i => input i + nudge i
    let score_change :=
      |GET_LINEAR_SCORE weights nudged_input - GET_LINEAR_SCORE weights input|
    let largest_change := size_limit * ∑ i, |weights i|
    score_change ≤ largest_change := by
  unfold_named_pieces
  have score_difference :
      GET_LINEAR_SCORE weights (fun i => input i + nudge i)
          - GET_LINEAR_SCORE weights input
        = ∑ i, weights i * nudge i := by
    simp only [GET_LINEAR_SCORE, mul_add, Finset.sum_add_distrib,
      add_sub_cancel_left]
  rw [score_difference, Finset.mul_sum]
  -- Bound each term of the sum, then add the bounds up.
  refine (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (nudge_is_small i) (abs_nonneg _)

end Adversarial

/-! ### Temperature -/

section Temperature

variable {Classes : Type*} [Fintype Classes] [Nonempty Classes]

/-- A larger score has a larger share. -/
theorem softmax_le_softmax_iff
    (scores : Classes → ℝ)
    (first_class second_class : Classes) :
    let first_share   := APPLY_SOFTMAX scores first_class
    let second_share  := APPLY_SOFTMAX scores second_class
    let share_order   := first_share ≤ second_share
    let score_order   := scores first_class ≤ scores second_class
    share_order ↔ score_order := by
  unfold_named_pieces
  rw [APPLY_SOFTMAX, APPLY_SOFTMAX,
    div_le_div_iff_of_pos_right (sum_exp_pos scores), Real.exp_le_exp]

/-- **Temperature changes confidence, never the ranking.** -/
theorem softmax_temperature_order
    {temperature : ℝ}
    (temperature_pos : 0 < temperature)
    (scores : Classes → ℝ)
    (first_class second_class : Classes) :
    let cooled_scores : Classes → ℝ := fun class_index => scores class_index / temperature
    let cooled_first   := APPLY_SOFTMAX cooled_scores first_class
    let cooled_second  := APPLY_SOFTMAX cooled_scores second_class
    let first_share    := APPLY_SOFTMAX scores first_class
    let second_share   := APPLY_SOFTMAX scores second_class
    let cooled_order   := cooled_first ≤ cooled_second
    let share_order    := first_share ≤ second_share
    cooled_order ↔ share_order := by
  unfold_named_pieces
  have share_order_iff (some_scores : Classes → ℝ) :
      APPLY_SOFTMAX some_scores first_class
          ≤ APPLY_SOFTMAX some_scores second_class
        ↔ some_scores first_class ≤ some_scores second_class :=
    softmax_le_softmax_iff some_scores first_class second_class
  rw [share_order_iff, share_order_iff,
    div_le_div_iff_of_pos_right temperature_pos]

end Temperature

/-! ### A critic of slope one -/

section Critic

variable {Inputs Pairs : Type*} [PseudoMetricSpace Inputs]

/-- **A critic of slope one cannot report more than the distance.** Pair each
real sample with a made one. The total gap in the critic's scores is at most the
total distance between the pairs. -/
theorem sum_critic_gap_le
    {critic : Inputs → ℝ}
    (critic_has_slope_one : LipschitzWith 1 critic)
    (pairs : Finset Pairs)
    (real_samples made_samples : Pairs → Inputs) :
    let total_gap :=
      ∑ i ∈ pairs, (critic (real_samples i) - critic (made_samples i))
    let total_distance :=
      ∑ i ∈ pairs, dist (real_samples i) (made_samples i)
    total_gap ≤ total_distance := by
  unfold_named_pieces
  refine Finset.sum_le_sum fun i _ => ?_
  have score_change :=
    critic_has_slope_one.dist_le_mul (real_samples i) (made_samples i)
  rw [Real.dist_eq, NNReal.coe_one, one_mul] at score_change
  exact (le_abs_self _).trans score_change

end Critic

end SquigglyLine
