/-
Squiggly below, flat above: the kernel trick.

A model that is linear in its weights first lifts the input to a feature
vector `features input`, usually in a space of many more dimensions, and
then takes the dot product (written `inner ℝ`) with its `weights`. Upstairs,
in the feature space, the model is a flat plane. Downstairs it is a squiggly
line. The weights are one arrow in the feature space, so the type `Weights`
is the type of the feature vectors too.

| Name                           | Meaning                                  |
|--------------------------------|------------------------------------------|
| `FeatureMap Inputs Weights`    | the lift: an input to its feature vector |
| `InputPerExample Examples Inputs` | one input for each training example   |
| `NumberPerExample Examples`    | one number for each training example     |
| `EVALUATE_FLAT_MODEL`          | the flat function upstairs               |
| `EVALUATE_LIFTED_MODEL`        | the model: lift, then the flat function  |
| `GET_LIFT_KERNEL`              | the overlap of two inputs upstairs       |

Theorems:

* `liftedModel_eq_comp` : the model is the flat function after the lift.
* `flatModel_blend` : the function upstairs is flat.
* `embed_mem_curve_liftedModel_iff` : a point is on the squiggly line exactly
  when its lift is on the flat plane.
* `boundary_eq_preimage` : the same for the boundary of a classifier.
* `abs_liftedModel_sub_le`, `lipschitzWith_liftedModel` : the slope of the
  line is at most the tilt of the plane times the stretch of the lift.
* `verticalDist_liftedModel_le` : so the slope sandwich reads in those two.
* `liftedModel_add_sum` : **the kernel trick.** Weights moved along the
  lifted data predict through the kernel alone.
* `liftKernel_comm`, `sum_sum_liftKernel_eq`, `sum_sum_liftKernel_nonneg` :
  such a kernel is symmetric and never negative.
* `exists_lift_eq` : any function is flat in some lift, so the statement says
  something only when the lift is fixed in advance.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import SquigglyLine.Theorem.Sandwich

namespace SquigglyLine

open NNReal

/-- A lift: it turns an input into a feature vector. The feature vectors
live in the same space as the weights.
Python: `Callable[[Input], Vector]`. -/
abbrev FeatureMap (Inputs Weights : Type*) := Inputs → Weights

/-- One input for each training example.
Python: `dict[Example, Input]`. -/
abbrev InputPerExample (Examples Inputs : Type*) := Examples → Inputs

/-- One number for each training example.
Python: `dict[Example, float]`. -/
abbrev NumberPerExample (Examples : Type*) := Examples → ℝ

variable {Inputs Weights : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]

/-- The flat function upstairs: the dot product of the weights with a
feature vector.
Python: `dot(weights, feature_vector)`. -/
def EVALUATE_FLAT_MODEL
    (weights : Weights)
    (feature_vector : Weights) : ℝ :=
  inner ℝ weights feature_vector

/-- A model linear in its weights: lift the input, then apply the flat
function.
Python: `dot(weights, features(input))`. -/
def EVALUATE_LIFTED_MODEL
    (features : FeatureMap Inputs Weights)
    (weights : Weights)
    (input : Inputs) : ℝ :=
  inner ℝ weights (features input)

/-- The kernel of a lift: how much two inputs overlap upstairs.
Python: `dot(features(input), features(other_input))`. -/
def GET_LIFT_KERNEL
    (features : FeatureMap Inputs Weights)
    (input : Inputs)
    (other_input : Inputs) : ℝ :=
  inner ℝ (features input) (features other_input)

/-! ### Flat above, squiggly below -/

section Flat

variable (features : FeatureMap Inputs Weights) (weights : Weights)

/-- The model downstairs is the flat function upstairs, applied after the
lift. -/
theorem liftedModel_eq_comp :
    let model_downstairs := EVALUATE_LIFTED_MODEL features weights
    let flat_after_lift  := EVALUATE_FLAT_MODEL weights ∘ features  -- `∘` chains two functions: lift first, then the flat one
    model_downstairs = flat_after_lift :=
  rfl

/-- **Flat above.** Upstairs, the value at a blend of two feature vectors is
the same blend of the two values. -/
theorem flatModel_blend
    (feature_vector : Weights)
    (other_vector : Weights)
    (fraction : ℝ) :
    let blended_vector :=
      (1 - fraction) • feature_vector + fraction • other_vector   -- `•` scales a vector by a number; the two shares add up to 1
    let value_at_blend := EVALUATE_FLAT_MODEL weights blended_vector
    let value_at_first := EVALUATE_FLAT_MODEL weights feature_vector
    let value_at_other := EVALUATE_FLAT_MODEL weights other_vector
    let blended_value  :=
      (1 - fraction) * value_at_first + fraction * value_at_other  -- the same shares, now of two numbers
    value_at_blend = blended_value := by
  unfold_named_pieces
  simp only [EVALUATE_FLAT_MODEL, inner_add_right, inner_smul_right]

/-- **The squiggly line is the flat plane, seen through the lift.** A point
is on the line downstairs exactly when its lift is on the plane upstairs. -/
theorem embed_mem_curve_liftedModel_iff
    (data_point : DataPoint Inputs) :
    let squiggly_line := GET_GRAPH (EVALUATE_LIFTED_MODEL features weights)
    let flat_plane    := GET_GRAPH (EVALUATE_FLAT_MODEL weights)
    let lifted_point : DataPoint Weights :=
      (features data_point.1, data_point.2)                       -- lift the input (`.1`), keep the label (`.2`)
    let is_on_the_line  := EMBED_DATA_POINT data_point ∈ squiggly_line
    let is_on_the_plane := EMBED_DATA_POINT lifted_point ∈ flat_plane
    is_on_the_line ↔ is_on_the_plane := by
  unfold_named_pieces
  -- On either graph, "is on it" means "the label is the output".
  rw [propext (embed_mem_curve_iff _ _), propext (embed_mem_curve_iff _ _)]
  rfl

/-- **A squiggly boundary is a flat one upstairs.** The inputs a classifier
scores zero are the ones whose lifts lie on a flat plane through the
origin. -/
theorem boundary_eq_preimage :
    let squiggly_boundary :=
      {input | EVALUATE_LIFTED_MODEL features weights input = 0}  -- the inputs the classifier scores zero
    let flat_boundary :=
      {feature_vector | EVALUATE_FLAT_MODEL weights feature_vector = 0}  -- a flat plane through the origin
    let inputs_lifted_onto_it := features ⁻¹' flat_boundary       -- `⁻¹'`: every input that the lift sends into the set
    squiggly_boundary = inputs_lifted_onto_it :=
  rfl

end Flat

/-! ### Where the squiggle is -/

section Slope

/-- The line changes by at most the size of the weights times how far the
lift moves. -/
theorem abs_liftedModel_sub_le
    (features : FeatureMap Inputs Weights)
    (weights : Weights)
    (input : Inputs)
    (other_input : Inputs) :
    let output       := EVALUATE_LIFTED_MODEL features weights input
    let other_output := EVALUATE_LIFTED_MODEL features weights other_input
    let change_in_output := |output - other_output|
    let tilt         := ‖weights‖                                -- the size of the weights: how tilted the plane is
    let move_of_lift := ‖features input - features other_input‖  -- how far apart the two inputs are upstairs
    change_in_output ≤ tilt * move_of_lift := by
  unfold_named_pieces
  -- The change is one dot product, of the weights with the move upstairs.
  rw [EVALUATE_LIFTED_MODEL, EVALUATE_LIFTED_MODEL, ← inner_sub_right]
  exact abs_real_inner_le_norm _ _

/-- **Slope is tilt times stretch.** If the lift stretches distances by at
most `lift_slope_limit`, the line is no steeper than the size of the weights
times `lift_slope_limit`. -/
theorem lipschitzWith_liftedModel
    [PseudoMetricSpace Inputs]
    {features : FeatureMap Inputs Weights}
    {lift_slope_limit : SlopeLimit}
    (lift_slope_is_bounded : LipschitzWith lift_slope_limit features)
    (weights : Weights) :
    let tilt        := ‖weights‖₊              -- the size of the weights, kept as a number that is not negative
    let slope_limit := tilt * lift_slope_limit  -- tilt of the plane times stretch of the lift
    let model       := EVALUATE_LIFTED_MODEL features weights
    LipschitzWith slope_limit model :=
  LipschitzWith.of_dist_le_mul fun input other_input => by
    -- The lift moves the two inputs apart by at most its own slope limit.
    have lift_moves_little :
        ‖features input - features other_input‖
          ≤ lift_slope_limit * dist input other_input :=
      dist_eq_norm (features input) (features other_input) ▸
        lift_slope_is_bounded.dist_le_mul input other_input
    rw [Real.dist_eq, NNReal.coe_mul, coe_nnnorm, mul_assoc]
    -- The flat function upstairs multiplies that move by at most the tilt.
    exact (abs_liftedModel_sub_le features weights input other_input).trans
      (mul_le_mul_of_nonneg_left lift_moves_little (norm_nonneg weights))

/-- **The sandwich, in tilt and stretch.** The line can be nearer to a data
point than its vertical error only by the factor
`√(1 + (‖weights‖ * lift_slope_limit)²)`. -/
theorem verticalDist_liftedModel_le
    {Inputs : Type*}
    [SeminormedAddCommGroup Inputs]
    {features : FeatureMap Inputs Weights}
    {lift_slope_limit : SlopeLimit}
    (lift_slope_is_bounded : LipschitzWith lift_slope_limit features)
    (weights : Weights)
    (data_point : DataPoint Inputs) :
    let model            := EVALUATE_LIFTED_MODEL features weights
    let vertical_error   := GET_VERTICAL_ERROR model data_point
    let nearest_distance := GET_NEAREST_DISTANCE model data_point
    let slope_limit      := ‖weights‖ * lift_slope_limit  -- tilt of the plane times stretch of the lift
    let stretch          := √(1 + slope_limit ^ 2)        -- Pythagoras: 1 across, slope_limit up
    vertical_error ≤ stretch * nearest_distance := by
  unfold_named_pieces
  simpa using
    verticalDist_le_of_lipschitz
      (lipschitzWith_liftedModel lift_slope_is_bounded weights) data_point

end Slope

/-! ### The kernel trick -/

section Kernel

variable {Examples : Type*} (features : FeatureMap Inputs Weights)

/-- **The kernel trick.** Move the weights from `start_weights` along the
lifted data points, by `coefficients i` along the lift of `data_inputs i`.
The new prediction at any input is the old one plus the kernel between that
input and each data point, weighted by the coefficients. The lift itself is
never needed. -/
theorem liftedModel_add_sum
    (examples : Finset Examples)
    (start_weights : Weights)
    (data_inputs : InputPerExample Examples Inputs)
    (coefficients : NumberPerExample Examples)
    (input : Inputs) :
    let weight_change :=
      ∑ i ∈ examples, coefficients i • features (data_inputs i)   -- each lifted data point, scaled by its own number
    let end_weights    := start_weights + weight_change
    let new_prediction := EVALUATE_LIFTED_MODEL features end_weights input
    let old_prediction :=
      EVALUATE_LIFTED_MODEL features start_weights input
    let kernel_with_the_data :=
      ∑ i ∈ examples,
        coefficients i * GET_LIFT_KERNEL features (data_inputs i) input  -- only the kernel appears: no feature vector is left
    new_prediction = old_prediction + kernel_with_the_data := by
  unfold_named_pieces
  -- A dot product with a sum is the sum of the dot products.
  simp only [EVALUATE_LIFTED_MODEL, GET_LIFT_KERNEL, inner_add_left,
    sum_inner, inner_smul_left]
  rfl

/-- The kernel does not care which input comes first. -/
theorem liftKernel_comm
    (input : Inputs)
    (other_input : Inputs) :
    let kernel         := GET_LIFT_KERNEL features input other_input
    let swapped_kernel := GET_LIFT_KERNEL features other_input input
    kernel = swapped_kernel :=
  real_inner_comm _ _

/-- **A kernel summed over all pairs is a squared length.** Weigh the data
points by any numbers `coefficients`. The kernel summed over all pairs with
those weights is the squared length of one vector upstairs. -/
theorem sum_sum_liftKernel_eq
    (examples : Finset Examples)
    (data_inputs : InputPerExample Examples Inputs)
    (coefficients : NumberPerExample Examples) :
    let kernel_over_all_pairs :=
      ∑ i ∈ examples, ∑ j ∈ examples,
        coefficients i * coefficients j
          * GET_LIFT_KERNEL features (data_inputs i) (data_inputs j)  -- every pair `(i, j)`, a data point with itself included
    let vector_upstairs :=
      ∑ i ∈ examples, coefficients i • features (data_inputs i)   -- each lifted data point, scaled by its own number
    let squared_length := ‖vector_upstairs‖ ^ 2
    kernel_over_all_pairs = squared_length := by
  unfold_named_pieces
  -- The squared length is the dot product of the vector with itself.
  -- Multiply the two sums out, one pair at a time.
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, GET_LIFT_KERNEL]
  simp only [conj_trivial]
  ring

/-- **A kernel from a lift is never negative.** The kernel summed over all
pairs, with any weights, is a squared length, and a square is not
negative. -/
theorem sum_sum_liftKernel_nonneg
    (examples : Finset Examples)
    (data_inputs : InputPerExample Examples Inputs)
    (coefficients : NumberPerExample Examples) :
    let kernel_over_all_pairs :=
      ∑ i ∈ examples, ∑ j ∈ examples,
        coefficients i * coefficients j
          * GET_LIFT_KERNEL features (data_inputs i) (data_inputs j)  -- every pair `(i, j)`, a data point with itself included
    0 ≤ kernel_over_all_pairs := by
  unfold_named_pieces
  rw [sum_sum_liftKernel_eq]
  positivity

end Kernel

/-! ### The catch -/

/-- **Any function is flat in some lift.** Take the function itself as the
lift. So "flat upstairs" says something only when the lift is chosen before
the labels are seen. -/
theorem exists_lift_eq
    {Inputs : Type*}
    (model : Model Inputs) :
    ∃ features : FeatureMap Inputs ℝ,
      let lifted_model := EVALUATE_LIFTED_MODEL features 1  -- the feature is one number, and the weight is the number 1
      lifted_model = model :=
  ⟨model, by
    unfold_named_pieces
    funext input
    simp [EVALUATE_LIFTED_MODEL]⟩

end SquigglyLine
