/-
Symmetries: changes to the weights that leave the line alone.

When a change to the weights does not change the function, the loss has no
slope in that direction, and training moves at right angles to it. Three
cases, each a well-known fact about real networks.

Throughout, `inner ℝ gradient weights` is the dot product of two vectors
(Python: `dot(gradient, weights)`), `‖weights‖` is the length of a vector and
`scale • weights` multiplies every weight by `scale`.

Rescaling everything (weights that feed a normalisation,
`IS_SCALE_INVARIANT`):
* `inner_gradient_self_eq_zero` : if the loss does not change when the weights
  are rescaled, the gradient is at right angles to the weights.
* `norm_sq_sub_smul_of_inner_eq_zero` : so a gradient step adds
  `learning_rate² * ‖gradient‖²` to the squared size of the weights.
* `norm_le_norm_sub_smul` : the weights never get shorter.

Rescaling one layer against the next (two weights multiplied,
`first_weight * second_weight`, stepped by `TAKE_STEP_ON_FIRST_WEIGHT` and
`TAKE_STEP_ON_SECOND_WEIGHT`):
* `balance_after_step` : a gradient step changes
  `first_weight² - second_weight²` only by a factor
  `1 - learning_rate² * error²`.
* `balanced_stays_balanced` : layers of equal size stay of equal size.
* `abs_eq_abs_of_balanced` : and then each carries the same share of the
  slope.

Relabelling the hidden units (`EVALUATE_ONE_HIDDEN_LAYER`):
* `oneHiddenLayer_relabel` : shuffling the units of a hidden layer gives the
  same function.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import SquigglyLine.Style

namespace SquigglyLine

open Topology

/-! ### Types -/

/-- How each hidden unit reads the input: `read_input unit input` is the
number that unit computes from the input, before the activation.
Python: `Callable[[Unit, Input], float]`. -/
abbrev InputReaders (HiddenUnits Inputs : Type*) := HiddenUnits → Inputs → ℝ

/-- A reordering of the hidden units: each unit is sent to another, and no
two to the same one.
Python: a permutation, such as `[2, 0, 1]`. -/
abbrev Shuffle (HiddenUnits : Type*) := Equiv.Perm HiddenUnits

/-! ### Rescaling everything -/

section Scale

variable {Weights : Type*} [NormedAddCommGroup Weights]
  [InnerProductSpace ℝ Weights]

/-- A loss that does not change when all the weights are multiplied by a
positive number. The weights that feed a normalisation layer are like this.
Python: `all(loss(scale * weights) == loss(weights) for scale > 0)`. -/
def IS_SCALE_INVARIANT
    (loss : Weights → ℝ) : Prop :=
  ∀ scale : ℝ, 0 < scale →  -- positive: a negative scale would flip the weights, not only resize them
    ∀ weights,
      let rescaled_weights := scale • weights
      loss rescaled_weights = loss weights

/-- **The gradient is at right angles to the weights.** Here `gradient` is
the gradient of `loss` at `weights`, in the sense that the loss changes at
the rate `inner ℝ gradient weights` when the weights move along
themselves. -/
theorem inner_gradient_self_eq_zero
    {loss : Weights → ℝ}
    (loss_is_scale_invariant : IS_SCALE_INVARIANT loss)
    {weights gradient : Weights}
    (gradient_gives_the_rate :
      HasDerivAt
        (fun stretch : ℝ => loss (weights + stretch • weights))  -- the loss, as the weights are stretched along themselves
        (inner ℝ gradient weights)                               -- its rate of change ...
        0) :                                                     -- ... at no stretch at all
    let rate_along_the_weights := inner ℝ gradient weights
    rate_along_the_weights = 0 := by  -- a dot product of zero: at right angles
  unfold_named_pieces
  -- Stretching the weights is rescaling them, and that does not change the
  -- loss. So near zero stretch the loss is constant.
  have loss_is_constant_near_zero :
      (fun _ : ℝ => loss weights)
        =ᶠ[𝓝 0] fun stretch => loss (weights + stretch • weights) := by
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)]
      with stretch stretch_above_minus_one
    rw [show weights + stretch • weights = (1 + stretch) • weights by
      rw [add_smul, one_smul]]
    exact (loss_is_scale_invariant (1 + stretch)
      (by linarith [Set.mem_Ioi.mp stretch_above_minus_one]) weights).symm
  -- A constant changes at rate zero, and a rate of change is unique.
  exact (gradient_gives_the_rate.congr_of_eventuallyEq
    loss_is_constant_near_zero).unique (hasDerivAt_const 0 (loss weights))

/-- **A step at right angles makes the weights longer.** -/
theorem norm_sq_sub_smul_of_inner_eq_zero
    {weights gradient : Weights}
    (gradient_is_at_right_angles : inner ℝ gradient weights = 0)
    (learning_rate : ℝ) :
    let weights_after_step  := weights - learning_rate • gradient  -- one step of gradient descent
    let step_length_squared := learning_rate ^ 2 * ‖gradient‖ ^ 2
    ‖weights_after_step‖ ^ 2 = ‖weights‖ ^ 2 + step_length_squared := by  -- Pythagoras: the step is at right angles
  unfold_named_pieces
  rw [norm_sub_sq_real, inner_smul_right, real_inner_comm gradient weights,
    gradient_is_at_right_angles, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

/-- With such a loss, gradient descent never shortens the weights. -/
theorem norm_le_norm_sub_smul
    {weights gradient : Weights}
    (gradient_is_at_right_angles : inner ℝ gradient weights = 0)
    (learning_rate : ℝ) :
    let weights_after_step := weights - learning_rate • gradient
    ‖weights‖ ≤ ‖weights_after_step‖ := by
  unfold_named_pieces
  -- Lengths are not negative, so it is enough to compare their squares.
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [norm_sq_sub_smul_of_inner_eq_zero gradient_is_at_right_angles]
  exact le_add_of_nonneg_right (by positivity)

end Scale

/-! ### Rescaling one layer against the next -/

section Balance

/-- The error of the two-weight model `first_weight * second_weight` on one
label.
Python: `first_weight * second_weight - label`. -/
noncomputable abbrev GET_PRODUCT_ERROR
    (first_weight second_weight label : ℝ) : ℝ :=
  first_weight * second_weight - label

/-- The first weight after one gradient step on the loss `error² / 2`. The
slope of that loss in the first weight is `error * second_weight`.
Python: `first_weight - learning_rate * (error * second_weight)`. -/
noncomputable abbrev TAKE_STEP_ON_FIRST_WEIGHT
    (first_weight second_weight label learning_rate : ℝ) : ℝ :=
  first_weight - learning_rate *
    (GET_PRODUCT_ERROR first_weight second_weight label * second_weight)

/-- The second weight after the same gradient step. The slope of the loss in
the second weight is `error * first_weight`.
Python: `second_weight - learning_rate * (error * first_weight)`. -/
noncomputable abbrev TAKE_STEP_ON_SECOND_WEIGHT
    (first_weight second_weight label learning_rate : ℝ) : ℝ :=
  second_weight - learning_rate *
    (GET_PRODUCT_ERROR first_weight second_weight label * first_weight)

/-- **Training keeps the layers in balance.** The model is
`first_weight * second_weight` and the loss is `error² / 2`. One gradient
step changes `first_weight² - second_weight²` only at second order in the
step. -/
theorem balance_after_step
    (first_weight second_weight label learning_rate : ℝ) :
    let error := GET_PRODUCT_ERROR first_weight second_weight label
    let first_weight_after :=
      TAKE_STEP_ON_FIRST_WEIGHT first_weight second_weight label learning_rate
    let second_weight_after :=
      TAKE_STEP_ON_SECOND_WEIGHT first_weight second_weight label learning_rate
    let imbalance_before := first_weight ^ 2 - second_weight ^ 2  -- zero when the two layers have the same size
    let imbalance_after  := first_weight_after ^ 2 - second_weight_after ^ 2
    let shrink_factor    := 1 - learning_rate ^ 2 * error ^ 2  -- no first power of `learning_rate`: a small step barely moves it
    imbalance_after = imbalance_before * shrink_factor := by
  unfold_named_pieces
  unfold TAKE_STEP_ON_FIRST_WEIGHT TAKE_STEP_ON_SECOND_WEIGHT GET_PRODUCT_ERROR
  ring

/-- Two layers of equal size are still of equal size after a step. -/
theorem balanced_stays_balanced
    (first_weight second_weight label learning_rate : ℝ)
    (layers_are_balanced : first_weight ^ 2 = second_weight ^ 2) :
    let first_weight_after :=
      TAKE_STEP_ON_FIRST_WEIGHT first_weight second_weight label learning_rate
    let second_weight_after :=
      TAKE_STEP_ON_SECOND_WEIGHT first_weight second_weight label learning_rate
    first_weight_after ^ 2 = second_weight_after ^ 2 := by
  unfold_named_pieces
  -- The imbalance after the step is the imbalance before, times a factor.
  -- The imbalance before is zero.
  have imbalance_after_step :
      TAKE_STEP_ON_FIRST_WEIGHT first_weight second_weight label
          learning_rate ^ 2
        - TAKE_STEP_ON_SECOND_WEIGHT first_weight second_weight label
            learning_rate ^ 2
        = (first_weight ^ 2 - second_weight ^ 2)
          * (1 - learning_rate ^ 2
            * GET_PRODUCT_ERROR first_weight second_weight label ^ 2) :=
    balance_after_step first_weight second_weight label learning_rate
  rw [layers_are_balanced, sub_self, zero_mul] at imbalance_after_step
  exact sub_eq_zero.mp imbalance_after_step

/-- Balanced layers have the same size, so each carries the same share of the
slope `first_weight * second_weight`. -/
theorem abs_eq_abs_of_balanced
    {first_weight second_weight : ℝ}
    (layers_are_balanced : first_weight ^ 2 = second_weight ^ 2) :
    let first_size  := |first_weight|
    let second_size := |second_weight|
    first_size = second_size :=
  (sq_eq_sq_iff_abs_eq_abs first_weight second_weight).mp layers_are_balanced

end Balance

/-! ### Relabelling the hidden units -/

section Relabel

variable {HiddenUnits Inputs : Type*} [Fintype HiddenUnits]

/-- A network with one hidden layer. Unit `i` reads the input through
`read_input i`, applies the activation, and is weighted by `output_weights i`
on the way out.
Python: `sum(output_weights[i] * activation(read_input[i](input))
for i in hidden_units)`. -/
def EVALUATE_ONE_HIDDEN_LAYER
    (activation : RealFunction)
    (read_input : InputReaders HiddenUnits Inputs)
    (output_weights : HiddenUnits → ℝ)
    (input : Inputs) : ℝ :=
  ∑ i, output_weights i * activation (read_input i input)

/-- **Shuffling the hidden units gives the same function.** -/
theorem oneHiddenLayer_relabel
    (activation : RealFunction)
    (read_input : InputReaders HiddenUnits Inputs)
    (output_weights : HiddenUnits → ℝ)
    (shuffle : Shuffle HiddenUnits) :
    let shuffled_network :=
      EVALUATE_ONE_HIDDEN_LAYER activation
        (read_input ∘ shuffle) (output_weights ∘ shuffle)  -- both reordered the same way: each unit keeps its own output weight
    let original_network :=
      EVALUATE_ONE_HIDDEN_LAYER activation read_input output_weights
    shuffled_network = original_network := by
  unfold_named_pieces
  funext input
  -- A sum does not depend on the order of its terms.
  exact Equiv.sum_comp shuffle fun i =>
    output_weights i * activation (read_input i input)

end Relabel

end SquigglyLine
