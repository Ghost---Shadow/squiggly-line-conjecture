/-
Signed distance functions.

A signed distance function stores a shape as a field: at every point of
space, the distance to the nearest point of the shape, with a sign for the
side. The nearest-point distance of the theorem is this field, for the line,
read at the data points.

* `nearestDist_eq_distanceField` : the theorem's distance is the field.
* `lipschitzWith_distanceField` : the field never changes faster than one,
  however steep the line is.
* `distanceField_eq_zero_iff` : it is zero exactly on the line.
* `notMem_curve_of_dist_lt` : a step shorter than the field's value cannot
  reach the line. This is what sphere tracing relies on.
* `notMem_curve_of_dist_lt_verticalDist_div` : the height above the line,
  divided by `√(1 + K²)`, is a safe step too.
* `distanceField_lt_iff_mem_thickening` : the tube of radius `r` round the
  line is where the field is below `r`.
* `abs_signedDist` : the signed distance has the size of the field.
* `abs_signedDist_le_verticalDist`, `verticalDist_le_abs_signedDist` : the
  slope sandwich, as a statement about how far the height above the line is
  from a true signed distance.
-/
import SquigglyLine.Theorem.Sandwich

namespace SquigglyLine

open NNReal

variable {X : Type*} [SeminormedAddCommGroup X] {f : X → ℝ}

/-! ### The distance field of the line -/

/-- The distance field of the line: at each point of space, the distance to the nearest point
of the line. -/
noncomputable def GET_DISTANCE_FIELD (f : X → ℝ) (q : Ambient X) : ℝ :=
  Metric.infDist q (GET_GRAPH f)

/-- **The theorem's distance is the field, read at the data.** -/
theorem nearestDist_eq_distanceField (f : X → ℝ) (p : DataPoint X) :
    GET_NEAREST_DISTANCE f p = GET_DISTANCE_FIELD f (EMBED_DATA_POINT p) :=
  rfl

theorem distanceField_nonneg (f : X → ℝ) (q : Ambient X) : 0 ≤ GET_DISTANCE_FIELD f q :=
  Metric.infDist_nonneg

omit [SeminormedAddCommGroup X] in
/-- The line is never empty: it has a point above or below any point of space. -/
theorem curve_nonempty_of (f : X → ℝ) (q : Ambient X) : (GET_GRAPH f).Nonempty :=
  ⟨_, footpoint_mem_curve f (WithLp.ofLp q)⟩

/-- **The field is never steep.** It changes by at most the distance moved, however squiggly
the line is. -/
theorem lipschitzWith_distanceField (f : X → ℝ) : LipschitzWith 1 (GET_DISTANCE_FIELD f) :=
  Metric.lipschitz_infDist_pt (GET_GRAPH f)

theorem abs_distanceField_sub_le (f : X → ℝ) (q q' : Ambient X) :
    |GET_DISTANCE_FIELD f q - GET_DISTANCE_FIELD f q'| ≤ dist q q' := by
  simpa [Real.dist_eq] using (lipschitzWith_distanceField f).dist_le_mul q q'

/-- The graph of a continuous function is closed. -/
theorem isClosed_curve (hf : Continuous f) : IsClosed (GET_GRAPH f) := by
  have hset : GET_GRAPH f = {q : Ambient X | (WithLp.ofLp q).2 = f (WithLp.ofLp q).1} := by
    ext q
    exact embed_mem_curve_iff f (WithLp.ofLp q)
  rw [hset]
  exact isClosed_eq (continuous_snd.comp (WithLp.prod_continuous_ofLp 2 X ℝ))
    (hf.comp (continuous_fst.comp (WithLp.prod_continuous_ofLp 2 X ℝ)))

/-- **The field is zero exactly on the line.** -/
theorem distanceField_eq_zero_iff (hf : Continuous f) (q : Ambient X) :
    GET_DISTANCE_FIELD f q = 0 ↔ q ∈ GET_GRAPH f :=
  ((isClosed_curve hf).mem_iff_infDist_zero (curve_nonempty_of f q)).symm

/-- **A step shorter than the field cannot reach the line.** From `q`, every point nearer
than the field's value at `q` is off the line. -/
theorem notMem_curve_of_dist_lt {q q' : Ambient X} (h : dist q q' < GET_DISTANCE_FIELD f q) :
    q' ∉ GET_GRAPH f :=
  fun hmem => absurd h (not_lt.mpr (Metric.infDist_le_dist_of_mem hmem))

/-- **A safe step from the height alone.** For a line of slope at most `K`, a step shorter
than the height above the line divided by `√(1 + K²)` cannot reach the line. -/
theorem notMem_curve_of_dist_lt_verticalDist_div {K : ℝ≥0} (hf : LipschitzWith K f)
    {p : DataPoint X} {q' : Ambient X}
    (h : dist (EMBED_DATA_POINT p) q' < GET_VERTICAL_ERROR f p / √(1 + (K : ℝ) ^ 2)) : q' ∉ GET_GRAPH f := by
  refine notMem_curve_of_dist_lt (h.trans_le ?_)
  rw [div_le_iff₀' (by positivity)]
  exact verticalDist_le_of_lipschitz hf p

/-- The tube of radius `r` round the line is where the field is below `r`. -/
theorem distanceField_lt_iff_mem_thickening (f : X → ℝ) (q : Ambient X) (r : ℝ) :
    GET_DISTANCE_FIELD f q < r ↔ q ∈ Metric.thickening r (GET_GRAPH f) :=
  (Metric.mem_thickening_iff_infDist_lt (curve_nonempty_of f q)).symm

/-! ### With a sign -/

/-- The signed distance from a data point to the line: positive above it, negative below. -/
noncomputable def GET_SIGNED_DISTANCE (f : X → ℝ) (p : DataPoint X) : ℝ :=
  (SignType.sign (p.2 - f p.1) : ℝ) * GET_NEAREST_DISTANCE f p

/-- The signed distance has the size of the nearest-point distance. -/
theorem abs_signedDist (f : X → ℝ) (p : DataPoint X) : |GET_SIGNED_DISTANCE f p| = GET_NEAREST_DISTANCE f p := by
  have hnonneg : 0 ≤ GET_NEAREST_DISTANCE f p := Metric.infDist_nonneg
  rcases lt_trichotomy (p.2 - f p.1) 0 with hbelow | hon | habove
  · simp [GET_SIGNED_DISTANCE, sign_neg hbelow, abs_of_nonneg hnonneg]
  · have hvertical : GET_VERTICAL_ERROR f p = 0 := by simp [GET_RESIDUAL_LOSS, hon]
    have hzero : GET_NEAREST_DISTANCE f p = 0 :=
      le_antisymm (hvertical ▸ nearestDist_le_verticalDist f p) hnonneg
    simp [GET_SIGNED_DISTANCE, hzero]
  · simp [GET_SIGNED_DISTANCE, sign_pos habove, abs_of_nonneg hnonneg]

/-- **The height above the line overstates the distance.** -/
theorem abs_signedDist_le_verticalDist (f : X → ℝ) (p : DataPoint X) :
    |GET_SIGNED_DISTANCE f p| ≤ GET_VERTICAL_ERROR f p :=
  abs_signedDist f p ▸ nearestDist_le_verticalDist f p

/-- **And by no more than the slope allows.** For a line of slope at most `K`, the height is
at most `√(1 + K²)` times the signed distance. -/
theorem verticalDist_le_abs_signedDist {K : ℝ≥0} (hf : LipschitzWith K f) (p : DataPoint X) :
    GET_VERTICAL_ERROR f p ≤ √(1 + (K : ℝ) ^ 2) * |GET_SIGNED_DISTANCE f p| :=
  abs_signedDist f p ▸ verticalDist_le_of_lipschitz hf p

end SquigglyLine
