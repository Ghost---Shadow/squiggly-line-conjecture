/-
The tube argument, made exact.

Draw a tube of radius `r` around a set `S` (the line). The mean distance from a
random point to `S` is the uncovered mass, integrated over all radii:

    E[dist(P, S)] = ∫₀^∞ P(P is outside the tube of radius r) dr

This replaces the earlier estimate `(uncovered fraction)^(1/d)`, which had no derivation.
It holds for every set `S` in every metric space, so it covers curves,
surfaces and hidden-state trajectories alike.
-/
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Topology.MetricSpace.Thickening
import SquigglyLine.Theorem.Defs

namespace SquigglyLine

open MeasureTheory

variable {E : Type*} [PseudoMetricSpace E] {S : Set E}

/-- The part of the space that the tube of radius `r` around `S` does not reach. -/
def GET_UNCOVERED_SET (S : Set E) (r : ℝ) : Set E :=
  (Metric.cthickening r S)ᶜ

/-- A point is uncovered at radius `r` exactly when it is further than `r` from `S`. -/
theorem mem_uncovered_iff (hS : S.Nonempty) {r : ℝ} (hr : 0 ≤ r) {p : E} :
    p ∈ GET_UNCOVERED_SET S r ↔ r < Metric.infDist p S := by
  rw [GET_UNCOVERED_SET, Set.mem_compl_iff, Metric.mem_cthickening_iff, not_le, Metric.infDist,
    ENNReal.ofReal_lt_iff_lt_toReal hr (Metric.infEDist_ne_top hS)]

/-- **Tube identity.** Mean distance to `S` is the uncovered mass integrated over radii. -/
theorem integral_infDist_eq_integral_uncovered [MeasurableSpace E] {μ : Measure E}
    (hS : S.Nonempty) (hint : Integrable (fun p => Metric.infDist p S) μ) :
    ∫ p, Metric.infDist p S ∂μ = ∫ r in Set.Ioi 0, μ.real (GET_UNCOVERED_SET S r) := by
  rw [hint.integral_eq_integral_meas_lt (ae_of_all _ fun _ => Metric.infDist_nonneg)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  congr 1
  ext p
  exact (mem_uncovered_iff hS (le_of_lt hr)).symm

end SquigglyLine
