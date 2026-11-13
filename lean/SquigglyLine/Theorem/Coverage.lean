/-
The tube identity.

Put a tube of radius `radius` around a set. The mean distance from a random
point to the set is the mass the tube has not yet reached, added up over all
radii:

    mean distance to the set = ∫ over radius > 0 of (mass not yet covered)

So "closer on average" and "covers more at every radius" are the same
statement. It holds for every set in every metric space, so it covers
curves, surfaces and hidden-state trajectories alike.

Definition: `GET_UNCOVERED_SET`.

Theorems: `mem_uncovered_iff`, `integral_infDist_eq_integral_uncovered`.
-/
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Topology.MetricSpace.Thickening
import SquigglyLine.Theorem.Defs

namespace SquigglyLine

open MeasureTheory

variable {Space : Type*} [PseudoMetricSpace Space] {target_set : Set Space}

/-- The part of the space that the tube of radius `radius` around the set
does not reach.
Python: `{point for point in space if dist_to_set(point) > radius}`. -/
def GET_UNCOVERED_SET (target_set : Set Space) (radius : ℝ) : Set Space :=
  let tube := Metric.cthickening radius target_set  -- every point within `radius` of the set
  tubeᶜ

/-- A point is uncovered at radius `radius` exactly when it is further than
`radius` from the set. -/
theorem mem_uncovered_iff
    (set_is_nonempty : target_set.Nonempty)  -- distance to an empty set has no meaning
    {radius : ℝ}
    (radius_nonneg : 0 ≤ radius)
    {point : Space} :
    let is_uncovered  := point ∈ GET_UNCOVERED_SET target_set radius
    let is_further    := radius < Metric.infDist point target_set
    is_uncovered ↔ is_further := by
  unfold_named_pieces
  rw [GET_UNCOVERED_SET, Set.mem_compl_iff, Metric.mem_cthickening_iff, not_le,
    Metric.infDist,
    ENNReal.ofReal_lt_iff_lt_toReal radius_nonneg
      (Metric.infEDist_ne_top set_is_nonempty)]

/-- **Tube identity.** Mean distance to the set is the uncovered mass
integrated over radii. -/
theorem integral_infDist_eq_integral_uncovered [MeasurableSpace Space]
    {point_distribution : Measure Space}
    (set_is_nonempty : target_set.Nonempty)
    (distance_is_integrable :
      Integrable (fun point => Metric.infDist point target_set)
        point_distribution) :  -- so the mean distance exists
    let mean_distance :=
      ∫ point, Metric.infDist point target_set ∂point_distribution
    let uncovered_mass := fun radius =>
      point_distribution.real (GET_UNCOVERED_SET target_set radius)
    let uncovered_mass_over_all_radii :=
      ∫ radius in Set.Ioi 0, uncovered_mass radius  -- `Set.Ioi 0`: every radius above zero
    mean_distance = uncovered_mass_over_all_radii := by
  unfold_named_pieces
  -- A mean is the integral of "how much mass lies above each level".
  rw [distance_is_integrable.integral_eq_integral_meas_lt
    (ae_of_all _ fun _ => Metric.infDist_nonneg)]
  refine setIntegral_congr_fun measurableSet_Ioi fun radius radius_pos => ?_
  congr 1
  ext point
  exact (mem_uncovered_iff set_is_nonempty (le_of_lt radius_pos)).symm

end SquigglyLine
