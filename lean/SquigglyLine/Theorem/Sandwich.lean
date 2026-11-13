/-
The slope sandwich.

For a `K`-Lipschitz function the two distances control each other:

    verticalDist / √(1 + K²)  ≤  nearestDist  ≤  verticalDist

So a line can be much nearer to the data than its vertical error only if it is
steep. Squiggliness buys nearness with slope and with nothing else.
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Lipschitz
import SquigglyLine.Theorem.Defs

namespace SquigglyLine

open NNReal

variable {X : Type*} [SeminormedAddCommGroup X] {f : X → ℝ}

/-- The line is never further away than the vertical error. -/
theorem nearestDist_le_verticalDist (f : X → ℝ) (p : DataPoint X) :
    GET_NEAREST_DISTANCE f p ≤ GET_VERTICAL_ERROR f p :=
  calc GET_NEAREST_DISTANCE f p
      ≤ dist (EMBED_DATA_POINT p) (EMBED_DATA_POINT (p.1, f p.1)) :=
        Metric.infDist_le_dist_of_mem (footpoint_mem_curve f p)
    _ = GET_VERTICAL_ERROR f p := by
        simp [dist_embed, GET_RESIDUAL_LOSS, Real.dist_eq, Real.sqrt_sq_eq_abs]

/-- Cauchy–Schwarz in the plane, in the form that the lower bound needs. -/
private theorem add_mul_le_sqrt_mul_sqrt (a b k : ℝ) :
    b + k * a ≤ √(1 + k ^ 2) * √(a ^ 2 + b ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (k * b - a)])

/-- The vertical error is at most `√(1 + K²)` times the distance to the line. -/
theorem verticalDist_le_of_lipschitz {K : ℝ≥0} (hf : LipschitzWith K f) (p : DataPoint X) :
    GET_VERTICAL_ERROR f p ≤ √(1 + (K : ℝ) ^ 2) * GET_NEAREST_DISTANCE f p := by
  have hpos : 0 < √(1 + (K : ℝ) ^ 2) := by positivity
  rw [← div_le_iff₀' hpos]
  refine (Metric.le_infDist ⟨_, footpoint_mem_curve f p⟩).2 ?_
  rintro _ ⟨x, rfl⟩
  rw [div_le_iff₀' hpos, dist_embed]
  calc GET_VERTICAL_ERROR f p
      = dist p.2 (f p.1) := (Real.dist_eq _ _).symm
    _ ≤ dist p.2 (f x) + dist (f x) (f p.1) := dist_triangle _ _ _
    _ ≤ dist p.2 (f x) + K * dist p.1 x := by
        gcongr
        exact dist_comm x p.1 ▸ hf.dist_le_mul x p.1
    _ ≤ √(1 + (K : ℝ) ^ 2) * √(dist p.1 x ^ 2 + dist p.2 (f x) ^ 2) :=
        add_mul_le_sqrt_mul_sqrt _ _ _

end SquigglyLine
