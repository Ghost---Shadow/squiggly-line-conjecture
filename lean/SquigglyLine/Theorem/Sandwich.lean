/-
The slope sandwich.

For a model whose slope is never more than `slope_limit`, the two distances
control each other:

    vertical_error / √(1 + slope_limit²)  ≤  nearest_distance  ≤  vertical_error

So a line can be much nearer to the data than its vertical error only if it
is steep. Squiggliness buys nearness with slope and with nothing else.

Theorems:

* `nearestDist_le_verticalDist`   the line is never further than straight up
                                  or down;
* `verticalDist_le_of_lipschitz`  the vertical error is at most
                                  `√(1 + slope_limit²)` times the distance.
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Lipschitz
import SquigglyLine.Theorem.Defs

namespace SquigglyLine

open NNReal

/-- The steepest a model is allowed to be: a number that is not negative. -/
abbrev SlopeLimit := ℝ≥0

variable {Inputs : Type*} [SeminormedAddCommGroup Inputs] {model : Model Inputs}

/-- The line is never further away than the vertical error. -/
theorem nearestDist_le_verticalDist
    (model : Model Inputs)
    (data_point : DataPoint Inputs) :
    let nearest_distance := GET_NEAREST_DISTANCE model data_point
    let vertical_error   := GET_VERTICAL_ERROR model data_point  -- straight up or down is one way to reach the line
    nearest_distance ≤ vertical_error := by
  unfold_named_pieces
  -- The point of the line directly above or below the data point.
  let footpoint :=
    EMBED_DATA_POINT (GET_INPUT data_point, model (GET_INPUT data_point))
  calc GET_NEAREST_DISTANCE model data_point
      ≤ dist (EMBED_DATA_POINT data_point) footpoint :=
        Metric.infDist_le_dist_of_mem (footpoint_mem_curve model data_point)
    _ = GET_VERTICAL_ERROR model data_point := by
        simp [footpoint, dist_embed, GET_RESIDUAL_LOSS, Real.dist_eq,
          Real.sqrt_sq_eq_abs]

/-- Cauchy–Schwarz in the plane, in the form that the lower bound needs. -/
private theorem add_mul_le_sqrt_mul_sqrt
    (across up slope : ℝ) :
    let climb_plus_drop := up + slope * across
    let steepness       := √(1 + slope ^ 2)       -- length of the step (1, slope)
    let step_length     := √(across ^ 2 + up ^ 2)  -- length of the step (across, up)
    climb_plus_drop ≤ steepness * step_length := by
  unfold_named_pieces
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (slope * up - across)])

/-- The vertical error is at most `√(1 + slope_limit²)` times the distance to
the line. -/
theorem verticalDist_le_of_lipschitz
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit model)
    (data_point : DataPoint Inputs) :
    let vertical_error   := GET_VERTICAL_ERROR model data_point
    let nearest_distance := GET_NEAREST_DISTANCE model data_point
    let stretch          := √(1 + (slope_limit : ℝ) ^ 2)  -- Pythagoras: 1 across, slope_limit up
    vertical_error ≤ stretch * nearest_distance := by
  unfold_named_pieces
  have stretch_pos : 0 < √(1 + (slope_limit : ℝ) ^ 2) := by positivity
  rw [← div_le_iff₀' stretch_pos]
  -- It is enough to compare with every point of the line, one at a time.
  refine (Metric.le_infDist ⟨_, footpoint_mem_curve model data_point⟩).2 ?_
  rintro _ ⟨input, rfl⟩
  rw [div_le_iff₀' stretch_pos, dist_embed]
  -- Go straight to the line at `input`, then follow the line back. The line
  -- climbs at most `slope_limit` per unit, so the detour is bounded.
  calc GET_VERTICAL_ERROR model data_point
      = dist data_point.2 (model data_point.1) := (Real.dist_eq _ _).symm
    _ ≤ dist data_point.2 (model input)
          + dist (model input) (model data_point.1) := dist_triangle _ _ _
    _ ≤ dist data_point.2 (model input)
          + slope_limit * dist data_point.1 input := by
        gcongr
        exact dist_comm input data_point.1 ▸
          slope_is_bounded.dist_le_mul input data_point.1
    _ ≤ √(1 + (slope_limit : ℝ) ^ 2)
          * √(dist data_point.1 input ^ 2
              + dist data_point.2 (model input) ^ 2) :=
        add_mul_le_sqrt_mul_sqrt _ _ _

end SquigglyLine
