/-
The dimpled manifold, in the squiggly line picture.

An input is a `position` on the data manifold together with a `height` off
it. Real data has height zero. A function that is `profile` along the
manifold and has slope `slope` across it is

    dimpled profile slope (position, height) = profile position + slope * height.

| Name                      | Meaning                                       |
|---------------------------|-----------------------------------------------|
| `DimpledInput Position`   | a position on the manifold and a height off it |
| `PLACE_ON_MANIFOLD`       | a real data input: height zero                |
| `EVALUATE_DIMPLED_MODEL`  | `profile` along, `slope` across               |
| `MAKE_DIMPLE`             | the input that steps straight off the manifold |

Theorems:

* `residualLoss_dimpled_onManifold`: on real data every loss is that of
  `profile`. Training cannot see `slope`.
* `dimpled_dimple`, `dist_onManifold_dimple`: for any data point and any
  label, the step `(label - profile position) / slope` straight off the
  manifold gives that label.
* `lipschitzWith_dimpled`: the dimpled function is no steeper than the two
  slopes added.
* `nearestDist_dimpled_bounds`: so the nearest-point distance lies between
  `vertical_error / √(1 + (profile_slope_limit + dimple_slope)²)` and
  `vertical_error / dimple_slope`.

The price of being close to the data is slope, and it can be paid entirely in
the direction that real data never visits. After Shamir, Melamed and
BenShmuel, "The Dimpled Manifold Model of Adversarial Examples" (2021).
-/
import SquigglyLine.Theorem.Sandwich

namespace SquigglyLine

open NNReal

/-- An input of the dimpled model: a position on the manifold and a height
off it.
Python: `tuple[Position, float]`. -/
abbrev DimpledInput (Position : Type*) := Position × ℝ

variable {Position : Type*} [SeminormedAddCommGroup Position]
  {profile : Model Position} {slope : ℝ}

/-- A real data input: a position on the manifold, at height zero.
Python: `(position, 0)`. -/
def PLACE_ON_MANIFOLD
    (position : Position) : DimpledInput Position :=
  (position, 0)

/-- A function that is `profile` along the manifold and has slope `slope`
across it.
Python: `lambda input: profile(input[0]) + slope * input[1]`. -/
def EVALUATE_DIMPLED_MODEL
    (profile : Model Position)
    (slope : ℝ) : Model (DimpledInput Position) :=
  fun input => profile input.1 + slope * input.2

/-- The adversarial input for the label `label`: step straight off the
manifold.
Python: `(position, (label - profile(position)) / slope)`. -/
noncomputable def MAKE_DIMPLE
    (profile : Model Position)
    (slope : ℝ)
    (position : Position)
    (label : ℝ) : DimpledInput Position :=
  (position, (label - profile position) / slope)

omit [SeminormedAddCommGroup Position] in
/-- On the manifold, the dimpled function is `profile`. -/
@[simp]
theorem dimpled_onManifold
    (profile : Model Position)
    (slope : ℝ)
    (position : Position) :
    let dimpled_model := EVALUATE_DIMPLED_MODEL profile slope
    let real_input    := PLACE_ON_MANIFOLD position
    dimpled_model real_input = profile position := by
  unfold_named_pieces
  simp [EVALUATE_DIMPLED_MODEL, PLACE_ON_MANIFOLD]

omit [SeminormedAddCommGroup Position] in
/-- **Training cannot see the slope off the manifold.** On real data, every
loss of the dimpled function is the loss of `profile`, whatever `slope`
is. -/
theorem residualLoss_dimpled_onManifold
    (loss_fn : RealFunction)
    (profile : Model Position)
    (slope : ℝ)
    (position : Position)
    (label : ℝ) :
    let dimpled_model := EVALUATE_DIMPLED_MODEL profile slope
    let data_point : DataPoint (DimpledInput Position) :=
      (PLACE_ON_MANIFOLD position, label)
    let loss_of_dimpled := GET_RESIDUAL_LOSS loss_fn dimpled_model data_point
    let loss_of_profile := loss_fn (label - profile position)
    loss_of_dimpled = loss_of_profile := by
  unfold_named_pieces
  simp [GET_RESIDUAL_LOSS]

omit [SeminormedAddCommGroup Position] in
/-- The adversarial step does not move along the manifold. -/
theorem dimple_fst
    (profile : Model Position)
    (slope : ℝ)
    (position : Position)
    (label : ℝ) :
    let dimple := MAKE_DIMPLE profile slope position label
    dimple.1 = position :=
  rfl

omit [SeminormedAddCommGroup Position] in
/-- **Any label is one step off the manifold.** -/
theorem dimpled_dimple
    (slope_ne_zero : slope ≠ 0)
    (position : Position)
    (label : ℝ) :
    let dimpled_model := EVALUATE_DIMPLED_MODEL profile slope
    let dimple        := MAKE_DIMPLE profile slope position label
    dimpled_model dimple = label := by
  unfold_named_pieces
  simp only [EVALUATE_DIMPLED_MODEL, MAKE_DIMPLE]
  field_simp
  ring

/-- The length of the adversarial step is the error divided by the slope. -/
theorem dist_onManifold_dimple
    (slope_pos : 0 < slope)
    (position : Position)
    (label : ℝ) :
    let real_input       := PLACE_ON_MANIFOLD position
    let dimple           := MAKE_DIMPLE profile slope position label
    let step_length      := dist real_input dimple
    let error_over_slope := |label - profile position| / slope  -- height needed to close the error, at that slope
    step_length = error_over_slope := by
  unfold_named_pieces
  simp [PLACE_ON_MANIFOLD, MAKE_DIMPLE, Prod.dist_eq, Real.dist_eq, abs_div,
    abs_of_pos slope_pos]
  exact div_nonneg (abs_nonneg _) slope_pos.le

/-- A dimpled function is `(profile_slope_limit + dimple_slope)`-Lipschitz
when `profile` is `profile_slope_limit`-Lipschitz. -/
theorem lipschitzWith_dimpled
    {profile_slope_limit : SlopeLimit}
    {dimple_slope : SlopeLimit}
    (profile_is_lipschitz : LipschitzWith profile_slope_limit profile) :
    let slope_limit   := profile_slope_limit + dimple_slope  -- the slope along the manifold plus the slope across it
    let dimpled_model := EVALUATE_DIMPLED_MODEL profile dimple_slope
    LipschitzWith slope_limit dimpled_model := by
  unfold_named_pieces
  refine LipschitzWith.of_dist_le_mul fun dimpled_input other_input => ?_
  -- Each of the two parts of an input is at most the whole distance away.
  have dist_position_le : dist dimpled_input.1 other_input.1
      ≤ dist dimpled_input other_input := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have dist_height_le : dist dimpled_input.2 other_input.2
      ≤ dist dimpled_input other_input := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  -- Split the change into a part along the manifold and a part across it.
  calc dist (EVALUATE_DIMPLED_MODEL profile dimple_slope dimpled_input)
        (EVALUATE_DIMPLED_MODEL profile dimple_slope other_input)
      = |(profile dimpled_input.1 - profile other_input.1)
          + dimple_slope * (dimpled_input.2 - other_input.2)| := by
        rw [Real.dist_eq]
        congr 1
        simp only [EVALUATE_DIMPLED_MODEL]
        ring
    _ ≤ |profile dimpled_input.1 - profile other_input.1|
          + |(dimple_slope : ℝ) * (dimpled_input.2 - other_input.2)| :=
        abs_add_le _ _
    _ = dist (profile dimpled_input.1) (profile other_input.1)
          + dimple_slope * dist dimpled_input.2 other_input.2 := by
        rw [abs_mul, abs_of_nonneg dimple_slope.coe_nonneg, Real.dist_eq,
          Real.dist_eq]
    _ ≤ profile_slope_limit * dist dimpled_input other_input
          + dimple_slope * dist dimpled_input other_input :=
        add_le_add
          ((profile_is_lipschitz.dist_le_mul _ _).trans
            (mul_le_mul_of_nonneg_left dist_position_le
              profile_slope_limit.coe_nonneg))
          (mul_le_mul_of_nonneg_left dist_height_le
            dimple_slope.coe_nonneg)
    _ = ((profile_slope_limit + dimple_slope : SlopeLimit) : ℝ)
          * dist dimpled_input other_input := by
        push_cast
        ring

/-- **The adversarial distance is the error over the slope.** For a real data
point, the nearest-point distance of a dimpled function lies between the
vertical error divided by `√(1 + (profile_slope_limit + dimple_slope)²)` and
the vertical error divided by `dimple_slope`. -/
theorem nearestDist_dimpled_bounds
    {profile_slope_limit : SlopeLimit}
    {dimple_slope : SlopeLimit}
    (profile_is_lipschitz : LipschitzWith profile_slope_limit profile)
    (dimple_slope_pos : 0 < (dimple_slope : ℝ))
    (position : Position)
    (label : ℝ) :
    let dimpled_model := EVALUATE_DIMPLED_MODEL profile dimple_slope
    let data_point : DataPoint (DimpledInput Position) :=
      (PLACE_ON_MANIFOLD position, label)
    let vertical_error   := GET_VERTICAL_ERROR dimpled_model data_point
    let nearest_distance := GET_NEAREST_DISTANCE dimpled_model data_point
    let total_slope_limit := profile_slope_limit + dimple_slope
    let stretch          := √(1 + (total_slope_limit : ℝ) ^ 2)  -- Pythagoras: 1 across, the total slope up
    let lower_bound      := vertical_error / stretch
    let upper_bound      := vertical_error / dimple_slope  -- the dimple step reaches the line after error / slope
    let is_above_lower   := lower_bound ≤ nearest_distance
    let is_below_upper   := nearest_distance ≤ upper_bound
    is_above_lower ∧ is_below_upper := by
  unfold_named_pieces
  constructor
  · -- The lower bound is the slope sandwich.
    rw [div_le_iff₀' (by positivity)]
    exact verticalDist_le_of_lipschitz
      (lipschitzWith_dimpled profile_is_lipschitz) _
  · -- The upper bound: the line has a point at the end of the dimple step.
    have dimpled_at_dimple :
        EVALUATE_DIMPLED_MODEL profile (dimple_slope : ℝ)
            (MAKE_DIMPLE profile (dimple_slope : ℝ) position label)
          = label :=
      dimpled_dimple dimple_slope_pos.ne' position label
    calc GET_NEAREST_DISTANCE (EVALUATE_DIMPLED_MODEL profile dimple_slope)
          (PLACE_ON_MANIFOLD position, label)
        ≤ dist (EMBED_DATA_POINT (PLACE_ON_MANIFOLD position, label))
            (EMBED_DATA_POINT
              (MAKE_DIMPLE profile dimple_slope position label,
                EVALUATE_DIMPLED_MODEL profile dimple_slope
                  (MAKE_DIMPLE profile dimple_slope position label))) :=
          Metric.infDist_le_dist_of_mem
            (footpoint_mem_curve _
              (MAKE_DIMPLE profile dimple_slope position label, label))
      _ = dist (PLACE_ON_MANIFOLD position)
            (MAKE_DIMPLE profile (dimple_slope : ℝ) position label) := by
          simp [dist_embed, dimpled_at_dimple, Real.sqrt_sq dist_nonneg]
      _ = |label - profile position| / dimple_slope :=
          dist_onManifold_dimple dimple_slope_pos position label
      _ = GET_VERTICAL_ERROR (EVALUATE_DIMPLED_MODEL profile dimple_slope)
            (PLACE_ON_MANIFOLD position, label) / dimple_slope := by
          simp [GET_RESIDUAL_LOSS]

end SquigglyLine
