/-
The distance field falls at rate exactly one.

`SignedDistance.lean` shows that the distance to the line changes by at most
one unit per unit moved. This file shows the bound is reached: walk from any
point straight to a nearest point of the line, and the distance falls by
exactly what you walk. So "slope at most one" cannot be improved, and a step
of sphere tracing along that path is as long as it can safely be.

Theorems:

* `infDist_toward_nearest` : a `fraction` of the way to a nearest point, the
  distance is the fraction `1 - fraction` of what it was;
* `infDist_sub_infDist_toward_nearest` : the fall in distance is the length
  walked;
* `exists_nearest_with_unit_rate` : in a space with compact closed balls
  such a nearest point exists;
* `not_lipschitzWith_infDist_of_lt_one` : no slope limit below one holds;
* `distanceField_toward_nearest` : the same, for the squiggly line.
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.Module
import SquigglyLine.Supporting.NetworkShape.SignedDistance

namespace SquigglyLine

open NNReal

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  {target_set : Set Space} {start_point nearest_point : Space}

/-- **Rate exactly one.** On the straight path from `start_point` to a nearest
point of the set, a fraction of the way along, the distance to the set is the
fraction `1 - fraction` of what it was. -/
theorem infDist_toward_nearest
    (nearest_is_in_set : nearest_point ∈ target_set)
    (nearest_is_closest :
      Metric.infDist start_point target_set = dist start_point nearest_point)
    {fraction : ℝ}
    (fraction_nonneg : 0 ≤ fraction)
    (fraction_le_one : fraction ≤ 1) :
    let walked_point    :=
      start_point + fraction • (nearest_point - start_point)
    let distance_now    := Metric.infDist walked_point target_set
    let distance_before := Metric.infDist start_point target_set
    let fraction_ahead  := 1 - fraction  -- the part of the path still to walk
    distance_now = fraction_ahead * distance_before := by
  unfold_named_pieces
  have length_walked :
      dist start_point
          (start_point + fraction • (nearest_point - start_point))
        = fraction * dist start_point nearest_point := by
    rw [dist_eq_norm, dist_eq_norm,
      show start_point
          - (start_point + fraction • (nearest_point - start_point))
        = fraction • (start_point - nearest_point) by module,
      norm_smul, Real.norm_of_nonneg fraction_nonneg]
  have length_ahead :
      dist (start_point + fraction • (nearest_point - start_point))
          nearest_point
        = (1 - fraction) * dist start_point nearest_point := by
    rw [dist_eq_norm, dist_eq_norm,
      show start_point + fraction • (nearest_point - start_point)
          - nearest_point
        = (1 - fraction) • (start_point - nearest_point) by module,
      norm_smul, Real.norm_of_nonneg (by linarith)]
  apply le_antisymm
  · -- The nearest point is still in the set, and it is `1 - fraction` of the
    -- old distance away.
    calc Metric.infDist
          (start_point + fraction • (nearest_point - start_point)) target_set
        ≤ dist (start_point + fraction • (nearest_point - start_point))
            nearest_point :=
          Metric.infDist_le_dist_of_mem nearest_is_in_set
      _ = (1 - fraction) * Metric.infDist start_point target_set := by
          rw [length_ahead, nearest_is_closest]
  · -- The distance cannot fall faster than one per unit walked.
    have distance_bound := Metric.infDist_le_infDist_add_dist (s := target_set)
      (x := start_point)
      (y := start_point + fraction • (nearest_point - start_point))
    rw [length_walked, ← nearest_is_closest] at distance_bound
    linarith

/-- The fall in distance equals the length walked. -/
theorem infDist_sub_infDist_toward_nearest
    (nearest_is_in_set : nearest_point ∈ target_set)
    (nearest_is_closest :
      Metric.infDist start_point target_set = dist start_point nearest_point)
    {fraction : ℝ}
    (fraction_nonneg : 0 ≤ fraction)
    (fraction_le_one : fraction ≤ 1) :
    let walked_point    :=
      start_point + fraction • (nearest_point - start_point)
    let distance_before := Metric.infDist start_point target_set
    let distance_now    := Metric.infDist walked_point target_set
    let fall            := distance_before - distance_now
    let length_walked   := dist start_point walked_point
    fall = length_walked := by
  unfold_named_pieces
  have length_walked :
      dist start_point
          (start_point + fraction • (nearest_point - start_point))
        = fraction * dist start_point nearest_point := by
    rw [dist_eq_norm, dist_eq_norm,
      show start_point
          - (start_point + fraction • (nearest_point - start_point))
        = fraction • (start_point - nearest_point) by module,
      norm_smul, Real.norm_of_nonneg fraction_nonneg]
  have rate_one :
      Metric.infDist (start_point + fraction • (nearest_point - start_point))
          target_set
        = (1 - fraction) * Metric.infDist start_point target_set :=
    infDist_toward_nearest nearest_is_in_set nearest_is_closest
      fraction_nonneg fraction_le_one
  rw [rate_one, length_walked, nearest_is_closest]
  ring

/-- In a space where closed balls are compact, every point has a nearest point
of a closed set, and the distance falls at rate one on the way to it. -/
theorem exists_nearest_with_unit_rate [ProperSpace Space]
    (set_is_closed : IsClosed target_set)
    (set_is_nonempty : target_set.Nonempty)
    (start_point : Space) :
    let falls_at_unit_rate := fun (nearest_point : Space) (fraction : ℝ) =>
      Metric.infDist (start_point + fraction • (nearest_point - start_point))
          target_set
        = (1 - fraction) * Metric.infDist start_point target_set
    ∃ nearest_point ∈ target_set, ∀ fraction : ℝ, 0 ≤ fraction →
      fraction ≤ 1 → falls_at_unit_rate nearest_point fraction := by
  unfold_named_pieces
  beta_reduce
  obtain ⟨nearest_point, nearest_is_in_set, nearest_is_closest⟩ :=
    set_is_closed.exists_infDist_eq_dist set_is_nonempty start_point
  exact ⟨nearest_point, nearest_is_in_set,
    fun fraction fraction_nonneg fraction_le_one =>
      infDist_toward_nearest nearest_is_in_set nearest_is_closest
        fraction_nonneg fraction_le_one⟩

omit [NormedSpace ℝ Space] in
/-- **The bound "slope at most one" cannot be improved.** If some point off the
set has a nearest point in it, the distance to the set has no slope limit
below one. -/
theorem not_lipschitzWith_infDist_of_lt_one
    (nearest_is_in_set : nearest_point ∈ target_set)
    (nearest_is_closest :
      Metric.infDist start_point target_set = dist start_point nearest_point)
    (start_is_off_set : 0 < dist start_point nearest_point)
    {slope_limit : SlopeLimit}
    (slope_limit_lt_one : slope_limit < 1) :
    let is_lipschitz := LipschitzWith slope_limit
      (fun point => Metric.infDist point target_set)
    ¬ is_lipschitz := by
  unfold_named_pieces
  intro is_lipschitz
  -- Walk all the way to the nearest point: the distance falls from
  -- `dist start_point nearest_point` to zero.
  have distance_change := is_lipschitz.dist_le_mul start_point nearest_point
  have distance_at_nearest : Metric.infDist nearest_point target_set = 0 :=
    Metric.infDist_zero_of_mem nearest_is_in_set
  rw [Real.dist_eq, distance_at_nearest, sub_zero, nearest_is_closest,
    abs_of_pos start_is_off_set] at distance_change
  have slope_limit_lt_one_real : (slope_limit : ℝ) < 1 := by
    exact_mod_cast slope_limit_lt_one
  nlinarith

section Line

variable {Inputs : Type*} [NormedAddCommGroup Inputs] [NormedSpace ℝ Inputs]
  {model : Model Inputs}

/-- **For the squiggly line.** From a point of space toward a nearest point of
the line, the distance field falls by exactly the distance walked. -/
theorem distanceField_toward_nearest
    {start_point nearest_point : Ambient Inputs}
    (nearest_is_on_line : nearest_point ∈ GET_GRAPH model)
    (nearest_is_closest :
      GET_DISTANCE_FIELD model start_point = dist start_point nearest_point)
    {fraction : ℝ}
    (fraction_nonneg : 0 ≤ fraction)
    (fraction_le_one : fraction ≤ 1) :
    let walked_point   :=
      start_point + fraction • (nearest_point - start_point)
    let field_now      := GET_DISTANCE_FIELD model walked_point
    let field_before   := GET_DISTANCE_FIELD model start_point
    let fraction_ahead := 1 - fraction  -- the part of the path still to walk
    field_now = fraction_ahead * field_before := by
  unfold_named_pieces
  exact infDist_toward_nearest nearest_is_on_line nearest_is_closest
    fraction_nonneg fraction_le_one

end Line

end SquigglyLine
