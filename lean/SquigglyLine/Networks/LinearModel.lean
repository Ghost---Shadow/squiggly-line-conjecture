/-
Where "a bigger model starts closer" is true: parameter space.

Take a model whose outputs on the data are linear in its weights, such as a
Fourier series in its coefficients: `predict weights` is the vector of
outputs, `labels` the vector of labels, and
`GET_RESIDUAL predict labels weights = labels - predict weights` is what is
left to fit.

In the terms of statistics this is a generalized linear model with no link
function and squared error, that is, linear regression on the features
`predict`.

* `residual_along`: on the straight path from `start_weights` to a fit
  `end_weights`, the residual shrinks in proportion. Every model walks the
  same loss curve.
* `exists_within_budget`: so moving a distance `budget` from the start
  removes the fraction `budget / ‖end_weights - start_weights‖` of the
  residual. Loss gap = distance × steepness: the nearer the fit, the more a
  fixed budget of movement buys.
* `travel_coprod_le`: adding weights never moves the nearest fit further
  away. A bigger model can always do what the smaller one did.

Together with `Marginal.lean`: at budget zero a bigger random model is no
closer to the data, and at every positive budget it is at least as close.
How much closer (measured: travel falls like `1 / √parameters`) is not proved
here.

| Name                | Meaning                                            |
|---------------------|----------------------------------------------------|
| `LinearPredictor`   | a model whose outputs are linear in its weights    |
| `GET_RESIDUAL`      | `labels - predict(weights)`: what is left to fit   |
| `MOVE_ALONG`        | the weights part of the way from a start to an end |
| `GET_FIT_DISTANCES` | how far from the start each fit of the data lies   |
| `GET_TRAVEL`        | the distance from the start to the nearest fit     |

How to read the notation:

* `Weights` and `Outputs` are spaces of vectors. Python: numpy arrays of a
  fixed length. The square brackets after them say that such vectors can be
  added, scaled by a real number, and measured for length.
* `‖vector‖` is the length of a vector. Python: `np.linalg.norm(vector)`.
* `number • vector` scales a vector. Python: `number * vector`.
* `predict weights` is the model's vector of outputs. Python:
  `matrix @ weights`.
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Module
import SquigglyLine.Style

namespace SquigglyLine

/-! ## Types -/

/-- A model whose outputs on the data are linear in its weights: doubling the
weights doubles the outputs, and adding weights adds outputs.
Python: `lambda weights: matrix @ weights`. -/
abbrev LinearPredictor
    (Weights : Type*)
    (Outputs : Type*)
    [NormedAddCommGroup Weights]
    [NormedSpace ℝ Weights]
    [NormedAddCommGroup Outputs]
    [NormedSpace ℝ Outputs] :=
  Weights →ₗ[ℝ] Outputs

-- Given, for everything below: three spaces of vectors. `ExtraWeights` holds
-- the weights that a bigger model adds.
variable
  {Weights : Type*}
  {ExtraWeights : Type*}
  {Outputs : Type*}
  [NormedAddCommGroup Weights] [NormedSpace ℝ Weights]
  [NormedAddCommGroup ExtraWeights] [NormedSpace ℝ ExtraWeights]
  [NormedAddCommGroup Outputs] [NormedSpace ℝ Outputs]

/-! ## The residual, and the straight path to a fit -/

/-- What is left to fit: the labels minus the model's outputs.
Python: `labels - predict(weights)`. -/
def GET_RESIDUAL
    (predict : LinearPredictor Weights Outputs)
    (labels : Outputs)
    (weights : Weights) : Outputs :=
  labels - predict weights

/-- The weights a fraction of the way from `start_weights` to `end_weights`:
fraction 0 is the start and fraction 1 is the end.
Python: `start_weights + fraction * (end_weights - start_weights)`. -/
def MOVE_ALONG
    (start_weights : Weights)
    (end_weights : Weights)
    (fraction : ℝ) : Weights :=
  let whole_step := end_weights - start_weights  -- the arrow from the start to the end
  start_weights + fraction • whole_step          -- `•` scales a vector by a number

-- Given, for everything below: a linear model, the labels to fit, and two
-- weight vectors, where a path starts and where it ends.
variable
  (predict : LinearPredictor Weights Outputs)
  (labels : Outputs)
  (start_weights : Weights)
  (end_weights : Weights)

/-- **Every model walks the same loss curve.** On the straight path to a fit,
the residual is the starting residual scaled by `1 - fraction`. -/
theorem residual_along
    (end_weights_fit : predict end_weights = labels)
    (fraction : ℝ) :
    let weights_on_path    := MOVE_ALONG start_weights end_weights fraction
    let residual_on_path   := GET_RESIDUAL predict labels weights_on_path
    let residual_at_start  := GET_RESIDUAL predict labels start_weights
    let remaining_fraction := 1 - fraction  -- the part of the path still ahead
    residual_on_path = remaining_fraction • residual_at_start := by
  unfold_named_pieces
  -- The model is linear, so its outputs move in step with the weights. At
  -- the end of the path the outputs are the labels.
  simp only [GET_RESIDUAL, MOVE_ALONG, map_add, map_smul, map_sub,
    end_weights_fit]
  module

/-- The size of the residual falls in a straight line along the path to a
fit. -/
theorem norm_residual_along
    (end_weights_fit : predict end_weights = labels)
    {fraction : ℝ}
    (fraction_le_one : fraction ≤ 1) :                          -- the path stops at the fit and does not go past it
    let weights_on_path    := MOVE_ALONG start_weights end_weights fraction
    let residual_on_path   := ‖GET_RESIDUAL predict labels weights_on_path‖
    let residual_at_start  := ‖GET_RESIDUAL predict labels start_weights‖
    let remaining_fraction := 1 - fraction                      -- the part of the path still ahead
    residual_on_path = remaining_fraction * residual_at_start := by
  unfold_named_pieces
  rw [residual_along predict labels start_weights end_weights
      end_weights_fit,
    norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr fraction_le_one)]

/-- A fraction of the way along the path is that fraction of the whole
distance away from the start. -/
theorem norm_along_sub
    {fraction : ℝ}
    (fraction_nonneg : 0 ≤ fraction) :                          -- the path goes forwards from the start
    let weights_on_path := MOVE_ALONG start_weights end_weights fraction
    let distance_moved  := ‖weights_on_path - start_weights‖
    let whole_distance  := ‖end_weights - start_weights‖
    distance_moved = fraction * whole_distance := by
  unfold_named_pieces
  simp [MOVE_ALONG, norm_smul, abs_of_nonneg fraction_nonneg]

/-- **Loss gap = distance × steepness.** If a fit lies at some distance from
the start, then moving a distance `budget`, no larger than that, removes the
fraction `budget / distance` of the residual. -/
theorem exists_within_budget
    (end_weights_fit : predict end_weights = labels)
    (end_is_not_start : end_weights ≠ start_weights)            -- so the distance to the fit is not zero
    {budget : ℝ}
    (budget_nonneg : 0 ≤ budget)
    (budget_le_distance_to_fit : budget ≤ ‖end_weights - start_weights‖) :
    let distance_to_fit   := ‖end_weights - start_weights‖
    let fraction_removed  := budget / distance_to_fit           -- the share of the path that the budget pays for
    let residual_at_start := ‖GET_RESIDUAL predict labels start_weights‖
    ∃ weights : Weights,
      let distance_moved := ‖weights - start_weights‖
      let residual_here  := ‖GET_RESIDUAL predict labels weights‖
      let spends_the_budget := distance_moved = budget
      let residual_has_shrunk :=
        residual_here = (1 - fraction_removed) * residual_at_start
      spends_the_budget ∧ residual_has_shrunk := by
  unfold_named_pieces
  have distance_to_fit_pos : 0 < ‖end_weights - start_weights‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr end_is_not_start)
  -- Walk the straight path towards the fit and stop when the budget is
  -- spent.
  refine ⟨MOVE_ALONG start_weights end_weights
    (budget / ‖end_weights - start_weights‖), ?_, ?_⟩
  · rw [norm_along_sub _ _
        (div_nonneg budget_nonneg distance_to_fit_pos.le),
      div_mul_cancel₀ _ distance_to_fit_pos.ne']
  · exact norm_residual_along predict labels start_weights end_weights
      end_weights_fit
      ((div_le_one distance_to_fit_pos).mpr budget_le_distance_to_fit)

/-! ## The distance to the nearest fit -/

/-- The distances from the start to the weight vectors that fit the data.
Python: `{norm(weights - start_weights) for weights in all_weights
if predict(weights) == labels}`. -/
def GET_FIT_DISTANCES : Set ℝ :=
  {distance | ∃ weights : Weights,
    let fits_the_data := predict weights = labels
    let is_this_far   := ‖weights - start_weights‖ = distance
    fits_the_data ∧ is_this_far}

/-- The distance in weight space from the start to the nearest fit.
Python: `min(GET_FIT_DISTANCES(predict, labels, start_weights))`. -/
noncomputable def GET_TRAVEL : ℝ :=
  sInf (GET_FIT_DISTANCES predict labels start_weights)  -- `sInf`: the smallest value, or the limit that the values come down to

/-- **More weights never move the fit away.** Extend the model with new
weights, with their own features `extra_predict`, starting at zero. The
nearest fit is then no further than before. -/
theorem travel_coprod_le
    (extra_predict : LinearPredictor ExtraWeights Outputs)
    (some_weights_fit : ∃ weights, predict weights = labels) :  -- otherwise there is no nearest fit to speak of
    let bigger_predict := predict.coprod extra_predict          -- the outputs of the old and the new weights, added
    let bigger_start   := (start_weights, (0 : ExtraWeights))   -- the new weights start at zero
    let travel_of_bigger_model :=
      GET_TRAVEL bigger_predict labels bigger_start
    let travel_of_smaller_model :=
      GET_TRAVEL predict labels start_weights
    travel_of_bigger_model ≤ travel_of_smaller_model := by
  unfold_named_pieces
  -- Every fit of the smaller model is also a fit of the bigger one, at the
  -- same distance: leave the new weights at zero. So the bigger model's
  -- nearest fit is at least as near.
  refine csInf_le_csInf ⟨0, ?_⟩ ?_ ?_
  · -- A distance is never negative, so the distances have a smallest value.
    rintro distance ⟨weights, -, rfl⟩
    exact norm_nonneg _
  · -- The smaller model has a fit, so it has a distance to compare.
    obtain ⟨weights, weights_fit⟩ := some_weights_fit
    exact ⟨_, weights, weights_fit, rfl⟩
  · rintro distance ⟨weights, weights_fit, rfl⟩
    exact ⟨(weights, 0), by simp [weights_fit], by simp [Prod.norm_def]⟩

end SquigglyLine
