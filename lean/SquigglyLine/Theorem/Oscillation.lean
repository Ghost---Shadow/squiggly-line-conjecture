/-
What "squiggly" has to mean for the conjecture to hold.

Say that a model covers the label range within `reach` when, near every
input and for every label in the range, some input at distance at most
`reach` is sent exactly to that label. The smallest such `reach` is the
oscillation scale of the model: how far one has to walk along the input to
see every label.

Two bounds pin the nearest-point distance to this scale:

    nearest_distance ≤ reach                                 (this file)
    vertical_error ≤ √(1 + slope_limit²) * nearest_distance  (`Sandwich.lean`)

So "closer to the data" is the same thing as "small oscillation scale", and
a small oscillation scale forces a large slope:
`vertical_error ≤ √(1 + slope_limit²) * reach`. The conjecture is therefore
a statement about how the oscillation scale of a random model depends on
the size of the model, and about nothing else.

Definition: `COVERS_WITHIN`.

Theorems:

* `nearestDist_nonneg`                            a distance is not negative;
* `nearestDist_le_of_coversWithin`                the covering bound;
* `verticalDist_le_of_lipschitz_of_coversWithin`  the slope tax;
* `exists_warp_of_coversWithin`                   nearness is used by moving
                                                  the input;
* `expected_nearestDist_nonneg`, `expected_nearestDist_le`  the same bounds
                                                  on average.
-/
import SquigglyLine.Theorem.RandomFunction
import SquigglyLine.Theorem.Sandwich

namespace SquigglyLine

open MeasureTheory NNReal

variable {Inputs : Type*} [SeminormedAddCommGroup Inputs]
  {model : Model Inputs} {reach : ℝ} {label_range : Set ℝ}

/-- Near every input, within distance `reach`, the model takes every label
in `label_range`.

    all(any(dist(input, other_input) <= reach and model(other_input) == label
            for other_input in all_inputs)
        for input in all_inputs for label in label_range)
-/
def COVERS_WITHIN
    (model : Model Inputs)
    (reach : ℝ)
    (label_range : Set ℝ) : Prop :=
  ∀ input, ∀ label ∈ label_range, ∃ other_input,
    let is_near        := dist input other_input ≤ reach
    let hits_the_label := model other_input = label
    is_near ∧ hits_the_label

/-- The distance to the nearest point of the line is never negative. -/
theorem nearestDist_nonneg
    (model : Model Inputs)
    (data_point : DataPoint Inputs) :
    let nearest_distance := GET_NEAREST_DISTANCE model data_point
    0 ≤ nearest_distance :=
  Metric.infDist_nonneg

/-- **Covering bound.** A model that covers the labels within `reach` is
within `reach` of every data point whose label is in range. -/
theorem nearestDist_le_of_coversWithin
    (model_covers : COVERS_WITHIN model reach label_range)
    (data_point : DataPoint Inputs)
    (label_in_range : GET_LABEL data_point ∈ label_range) :
    let nearest_distance := GET_NEAREST_DISTANCE model data_point
    nearest_distance ≤ reach := by
  unfold_named_pieces
  -- Some input within `reach` is sent exactly to this label. The line
  -- passes through that point, at the height of the data point.
  obtain ⟨other_input, other_is_near, other_hits_label⟩ :=
    model_covers data_point.1 data_point.2 label_in_range
  calc GET_NEAREST_DISTANCE model data_point
      ≤ dist (EMBED_DATA_POINT data_point)
          (EMBED_DATA_POINT (other_input, model other_input)) :=
        Metric.infDist_le_dist_of_mem
          (footpoint_mem_curve model (other_input, model other_input))
    _ = dist data_point.1 other_input := by
        simp [dist_embed, other_hits_label, Real.sqrt_sq dist_nonneg]
    _ ≤ reach := other_is_near

/-- **The slope tax.** Covering the labels within a short distance needs a
steep model: the vertical error is at most `√(1 + slope_limit²)` times the
oscillation scale. -/
theorem verticalDist_le_of_lipschitz_of_coversWithin
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit model)
    (model_covers : COVERS_WITHIN model reach label_range)
    (data_point : DataPoint Inputs)
    (label_in_range : GET_LABEL data_point ∈ label_range) :
    let vertical_error := GET_VERTICAL_ERROR model data_point
    let stretch        := √(1 + (slope_limit : ℝ) ^ 2)  -- Pythagoras: 1 across, slope_limit up
    vertical_error ≤ stretch * reach :=
  (verticalDist_le_of_lipschitz slope_is_bounded data_point).trans
    (mul_le_mul_of_nonneg_left
      (nearestDist_le_of_coversWithin model_covers data_point label_in_range)
      (Real.sqrt_nonneg _))

/-- **Nearness can be used, by moving the input.** If the model covers the
labels within `reach`, then any target with labels in range is fitted
exactly by the model after a warp of the input that moves no point by more
than `reach`. The loss at the start does not see the nearness; a small shift
of the input cashes it in. -/
theorem exists_warp_of_coversWithin
    (model_covers : COVERS_WITHIN model reach label_range)
    (target : Model Inputs)
    (target_in_range : ∀ input, target input ∈ label_range) :
    ∃ warp : WarpOver Inputs,
      let moves_each_input_a_little :=
        ∀ input, dist input (warp input) ≤ reach
      let hits_the_target :=
        ∀ input, model (warp input) = target input
      moves_each_input_a_little ∧ hits_the_target := by
  unfold_named_pieces
  -- For each input, pick a nearby input where the model has the target's
  -- value. Covering says there is one.
  choose warp warp_works using
    fun input => model_covers input (target input) (target_in_range input)
  exact ⟨warp, fun input => (warp_works input).1,
    fun input => (warp_works input).2⟩

section Expected

variable [MeasurableSpace Inputs]

/-- The expected distance to the nearest point is never negative. -/
theorem expected_nearestDist_nonneg
    (random_model : RandomFunction Inputs)
    (data_distribution : DataDistributionOver Inputs) :
    let expected_distance :=
      random_model.expected GET_NEAREST_DISTANCE data_distribution
    0 ≤ expected_distance :=
  integral_nonneg fun _ => integral_nonneg fun _ => nearestDist_nonneg _ _

/-- **Covering bound, in expectation.** If every draw of a random model
covers the labels within `reach`, its expected nearest-point distance is at
most `reach`, on any data whose labels are in range. -/
theorem expected_nearestDist_le
    (random_model : RandomFunction Inputs)
    (every_draw_covers :
      ∀ parameters,
        COVERS_WITHIN (random_model.eval parameters) reach label_range)
    (data_distribution : DataDistributionOver Inputs)
    [IsProbabilityMeasure data_distribution]  -- the probabilities add up to 1
    (labels_in_range :
      ∀ᵐ data_point ∂data_distribution,
        GET_LABEL data_point ∈ label_range) :
    let expected_distance :=
      random_model.expected GET_NEAREST_DISTANCE data_distribution
    expected_distance ≤ reach := by
  unfold_named_pieces
  -- For one data point: every draw is within `reach`, so the average over
  -- the draws is too.
  have average_over_draws_is_small :
      ∀ data_point : DataPoint Inputs, data_point.2 ∈ label_range →
        ∫ parameters,
            GET_NEAREST_DISTANCE (random_model.eval parameters) data_point
          ∂random_model.prior ≤ reach :=
    fun data_point label_in_range =>
      calc ∫ parameters,
              GET_NEAREST_DISTANCE (random_model.eval parameters) data_point
            ∂random_model.prior
          ≤ ∫ _, reach ∂random_model.prior :=
            integral_mono_of_nonneg
              (ae_of_all _ fun _ => nearestDist_nonneg _ _)
              (integrable_const reach)
              (ae_of_all _ fun parameters =>
                nearestDist_le_of_coversWithin (every_draw_covers parameters)
                  data_point label_in_range)
        _ = reach := by simp
  -- Then average over the data points.
  calc random_model.expected GET_NEAREST_DISTANCE data_distribution
      ≤ ∫ _, reach ∂data_distribution :=
        integral_mono_of_nonneg
          (ae_of_all _ fun _ =>
            integral_nonneg fun _ => nearestDist_nonneg _ _)
          (integrable_const reach)
          (labels_in_range.mono average_over_draws_is_small)
    _ = reach := by simp

end Expected

end SquigglyLine
