/-
Signed distance functions.

A signed distance function stores a shape as a field: at every point of
space, the distance to the nearest point of the shape, with a sign for the
side. The nearest-point distance of the theorem is this field, for the line,
read at the data points.

| Name                  | Meaning                                           |
|-----------------------|---------------------------------------------------|
| `GET_DISTANCE_FIELD`  | the distance from a point of space to the line    |
| `GET_SIGNED_DISTANCE` | the same for a data point, with a sign for a side |

Theorems:

* `nearestDist_eq_distanceField` : the theorem's distance is the field.
* `lipschitzWith_distanceField` : the field never changes faster than one,
  however steep the line is.
* `distanceField_eq_zero_iff` : it is zero exactly on the line.
* `notMem_curve_of_dist_lt` : a step shorter than the field's value cannot
  reach the line. This is what sphere tracing relies on.
* `notMem_curve_of_dist_lt_verticalDist_div` : the height above the line,
  divided by `√(1 + slope_limit²)`, is a safe step too.
* `distanceField_lt_iff_mem_thickening` : the tube of radius `radius` round
  the line is where the field is below `radius`.
* `abs_signedDist` : the signed distance has the size of the field.
* `abs_signedDist_le_verticalDist`, `verticalDist_le_abs_signedDist` : the
  slope sandwich, as a statement about how far the height above the line is
  from a true signed distance.
-/
import SquigglyLine.Theorem.Sandwich

namespace SquigglyLine

open NNReal

variable {Inputs : Type*} [SeminormedAddCommGroup Inputs]
  {model : Model Inputs}

/-! ### The distance field of the line -/

/-- The distance field of the line: at each point of space, the distance to
the nearest point of the line.
Python: `min(dist(ambient_point, point) for point in GET_GRAPH(model))`. -/
noncomputable def GET_DISTANCE_FIELD
    (model : Model Inputs)
    (ambient_point : Ambient Inputs) : ℝ :=
  Metric.infDist ambient_point (GET_GRAPH model)

/-- **The theorem's distance is the field, read at the data.** -/
theorem nearestDist_eq_distanceField
    (model : Model Inputs)
    (data_point : DataPoint Inputs) :
    let nearest_distance := GET_NEAREST_DISTANCE model data_point
    let field_value      :=
      GET_DISTANCE_FIELD model (EMBED_DATA_POINT data_point)
    nearest_distance = field_value :=
  rfl

/-- The field is never negative: a distance is not. -/
theorem distanceField_nonneg
    (model : Model Inputs)
    (ambient_point : Ambient Inputs) :
    let field_value := GET_DISTANCE_FIELD model ambient_point
    0 ≤ field_value := by
  unfold_named_pieces
  exact Metric.infDist_nonneg

omit [SeminormedAddCommGroup Inputs] in
/-- The line is never empty: it has a point above or below any point of
space. -/
theorem curve_nonempty_of
    (model : Model Inputs)
    (ambient_point : Ambient Inputs) :
    let line := GET_GRAPH model
    line.Nonempty := by
  unfold_named_pieces
  exact ⟨_, footpoint_mem_curve model (WithLp.ofLp ambient_point)⟩

/-- **The field is never steep.** It changes by at most the distance moved,
however squiggly the line is. -/
theorem lipschitzWith_distanceField
    (model : Model Inputs) :
    let field := GET_DISTANCE_FIELD model
    LipschitzWith 1 field := by  -- one unit of field per unit moved
  unfold_named_pieces
  exact Metric.lipschitz_infDist_pt (GET_GRAPH model)

/-- Moving from one point of space to another changes the field by at most
the distance between them. -/
theorem abs_distanceField_sub_le
    (model : Model Inputs)
    (ambient_point : Ambient Inputs)
    (other_point : Ambient Inputs) :
    let field_value       := GET_DISTANCE_FIELD model ambient_point
    let other_field_value := GET_DISTANCE_FIELD model other_point
    let change_in_field   := |field_value - other_field_value|
    let distance_moved    := dist ambient_point other_point
    change_in_field ≤ distance_moved := by
  unfold_named_pieces
  simpa [Real.dist_eq] using
    (lipschitzWith_distanceField model :
      LipschitzWith 1 (GET_DISTANCE_FIELD model)).dist_le_mul
      ambient_point other_point

/-- The graph of a continuous function is closed. -/
theorem isClosed_curve
    (model_is_continuous : Continuous model) :
    let line := GET_GRAPH model
    IsClosed line := by
  unfold_named_pieces
  -- The graph is the set of points whose label equals the model's output.
  have graph_is_equalizer :
      GET_GRAPH model
        = {ambient_point : Ambient Inputs |
            (WithLp.ofLp ambient_point).2
              = model (WithLp.ofLp ambient_point).1} := by
    ext ambient_point
    exact embed_mem_curve_iff model (WithLp.ofLp ambient_point)
  rw [graph_is_equalizer]
  exact isClosed_eq
    (continuous_snd.comp (WithLp.prod_continuous_ofLp 2 Inputs ℝ))
    (model_is_continuous.comp
      (continuous_fst.comp (WithLp.prod_continuous_ofLp 2 Inputs ℝ)))

/-- **The field is zero exactly on the line.** -/
theorem distanceField_eq_zero_iff
    (model_is_continuous : Continuous model)
    (ambient_point : Ambient Inputs) :
    let field_value     := GET_DISTANCE_FIELD model ambient_point
    let line            := GET_GRAPH model
    let field_is_zero   := field_value = 0
    let is_on_the_line  := ambient_point ∈ line
    field_is_zero ↔ is_on_the_line := by
  unfold_named_pieces
  exact
    ((isClosed_curve model_is_continuous : IsClosed (GET_GRAPH model)
      ).mem_iff_infDist_zero
      (curve_nonempty_of model ambient_point)).symm

/-- **A step shorter than the field cannot reach the line.** From
`ambient_point`, every point nearer than the field's value there is off the
line. -/
theorem notMem_curve_of_dist_lt
    {ambient_point : Ambient Inputs}
    {other_point : Ambient Inputs}
    (step_is_short :
      dist ambient_point other_point
        < GET_DISTANCE_FIELD model ambient_point) :
    let line := GET_GRAPH model
    other_point ∉ line := by
  unfold_named_pieces
  exact fun other_point_on_line =>
    absurd step_is_short
      (not_lt.mpr (Metric.infDist_le_dist_of_mem other_point_on_line))

/-- **A safe step from the height alone.** For a line of slope at most
`slope_limit`, a step shorter than the height above the line divided by
`√(1 + slope_limit²)` cannot reach the line. -/
theorem notMem_curve_of_dist_lt_verticalDist_div
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit model)
    {data_point : DataPoint Inputs}
    {other_point : Ambient Inputs}
    (step_is_short :
      dist (EMBED_DATA_POINT data_point) other_point
        < GET_VERTICAL_ERROR model data_point
          / √(1 + (slope_limit : ℝ) ^ 2)) :  -- the sandwich's lower bound
    let line := GET_GRAPH model
    other_point ∉ line := by
  unfold_named_pieces
  refine notMem_curve_of_dist_lt (step_is_short.trans_le ?_)
  rw [div_le_iff₀' (by positivity)]
  exact verticalDist_le_of_lipschitz slope_is_bounded data_point

/-- The tube of radius `radius` round the line is where the field is below
`radius`. -/
theorem distanceField_lt_iff_mem_thickening
    (model : Model Inputs)
    (ambient_point : Ambient Inputs)
    (radius : ℝ) :
    let field_value      := GET_DISTANCE_FIELD model ambient_point
    let tube             := Metric.thickening radius (GET_GRAPH model)
    let field_is_below   := field_value < radius
    let is_in_the_tube   := ambient_point ∈ tube
    field_is_below ↔ is_in_the_tube := by
  unfold_named_pieces
  exact
    (Metric.mem_thickening_iff_infDist_lt
      (curve_nonempty_of model ambient_point)).symm

/-! ### With a sign -/

/-- The signed distance from a data point to the line: positive above it,
negative below.
Python: `sign(label - model(input)) * GET_NEAREST_DISTANCE(model, data_point)`.
-/
noncomputable def GET_SIGNED_DISTANCE
    (model : Model Inputs)
    (data_point : DataPoint Inputs) : ℝ :=
  (SignType.sign (data_point.2 - model data_point.1) : ℝ)
    * GET_NEAREST_DISTANCE model data_point

/-- The signed distance has the size of the nearest-point distance. -/
theorem abs_signedDist
    (model : Model Inputs)
    (data_point : DataPoint Inputs) :
    let signed_distance  := GET_SIGNED_DISTANCE model data_point
    let nearest_distance := GET_NEAREST_DISTANCE model data_point
    |signed_distance| = nearest_distance := by
  unfold_named_pieces
  have distance_nonneg : 0 ≤ GET_NEAREST_DISTANCE model data_point :=
    Metric.infDist_nonneg
  -- Three cases: below the line, on it, above it.
  rcases lt_trichotomy (data_point.2 - model data_point.1) 0 with
    below_line | on_line | above_line
  · simp [GET_SIGNED_DISTANCE, sign_neg below_line,
      abs_of_nonneg distance_nonneg]
  · have vertical_is_zero : GET_VERTICAL_ERROR model data_point = 0 := by
      simp [GET_RESIDUAL_LOSS, on_line]
    have nearest_le_vertical :
        GET_NEAREST_DISTANCE model data_point
          ≤ GET_VERTICAL_ERROR model data_point :=
      nearestDist_le_verticalDist model data_point
    have distance_is_zero : GET_NEAREST_DISTANCE model data_point = 0 :=
      le_antisymm (vertical_is_zero ▸ nearest_le_vertical) distance_nonneg
    simp [GET_SIGNED_DISTANCE, distance_is_zero]
  · simp [GET_SIGNED_DISTANCE, sign_pos above_line,
      abs_of_nonneg distance_nonneg]

/-- **The height above the line overstates the distance.** -/
theorem abs_signedDist_le_verticalDist
    (model : Model Inputs)
    (data_point : DataPoint Inputs) :
    let signed_distance := GET_SIGNED_DISTANCE model data_point
    let vertical_error  := GET_VERTICAL_ERROR model data_point
    |signed_distance| ≤ vertical_error := by
  unfold_named_pieces
  have abs_is_nearest :
      |GET_SIGNED_DISTANCE model data_point|
        = GET_NEAREST_DISTANCE model data_point :=
    abs_signedDist model data_point
  have nearest_le_vertical :
      GET_NEAREST_DISTANCE model data_point
        ≤ GET_VERTICAL_ERROR model data_point :=
    nearestDist_le_verticalDist model data_point
  rw [abs_is_nearest]
  exact nearest_le_vertical

/-- **And by no more than the slope allows.** For a line of slope at most
`slope_limit`, the height is at most `√(1 + slope_limit²)` times the signed
distance. -/
theorem verticalDist_le_abs_signedDist
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit model)
    (data_point : DataPoint Inputs) :
    let vertical_error  := GET_VERTICAL_ERROR model data_point
    let signed_distance := GET_SIGNED_DISTANCE model data_point
    let stretch         := √(1 + (slope_limit : ℝ) ^ 2)  -- Pythagoras: 1 across, slope_limit up
    vertical_error ≤ stretch * |signed_distance| := by
  unfold_named_pieces
  have abs_is_nearest :
      |GET_SIGNED_DISTANCE model data_point|
        = GET_NEAREST_DISTANCE model data_point :=
    abs_signedDist model data_point
  have vertical_le_stretched :
      GET_VERTICAL_ERROR model data_point
        ≤ √(1 + (slope_limit : ℝ) ^ 2)
          * GET_NEAREST_DISTANCE model data_point :=
    verticalDist_le_of_lipschitz slope_is_bounded data_point
  rw [abs_is_nearest]
  exact vertical_le_stretched

end SquigglyLine
