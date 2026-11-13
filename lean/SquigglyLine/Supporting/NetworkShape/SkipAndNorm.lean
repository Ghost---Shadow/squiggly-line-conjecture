/-
Skip connections and normalisation, as polarizers.

`PASS_THROUGH_PLATE axis light` keeps the shadow of the light on the axis.
Light here lives in any real inner product space, so the statements hold for
any width. The overlap of the light with the axis is their dot product,
written `inner ℝ axis light`. The strength of the light is its length,
written `‖light‖`.

A skip connection is a plate with a bypass,
`PASS_THROUGH_SKIP_PLATE axis light = light + PASS_THROUGH_PLATE axis light`:
* `norm_le_norm_skipPlate` : it never dims the light.
* `skipPlate_of_crossed` : a crossed plate with a bypass does nothing, where a
  bare crossed plate blocks (`plate_of_crossed`).
* `inner_skipPlate`, `skipPlate_sub_plate` : it doubles the part along the
  axis and leaves the rest. The light turns part of the way.
* `inner_iterate_skipPlate`, `iterate_skipPlate_sub_plate` : `plate_count` of
  them bring the light ever closer to the axis and never onto it.

Normalisation is an amplifier, `RENORMALIZE light = ‖light‖⁻¹ • light`:
* `renorm_plate` : after a plate and an amplifier the light lies along the
  axis at full strength, for any turn short of a right angle.
* `throughNormedPlates_eq` : so a whole stack of plates with amplifiers
  delivers full strength along the last axis.
* `renorm_plate_of_crossed` : it cannot revive light that a crossed plate
  blocked.

| Name                         | Meaning                                    |
|------------------------------|--------------------------------------------|
| `PASS_THROUGH_PLATE`         | the shadow of the light on the axis        |
| `PASS_THROUGH_SKIP_PLATE`    | the light, plus its shadow on the axis     |
| `RENORMALIZE`                | the light, brought back to length one      |
| `PlateAxes Space`            | the axis of each plate of a stack          |
| `LightAfterEachPlate Space`  | the light after 0, 1, 2, ... plates        |
| `PASS_THROUGH_NORMED_PLATES` | a stack of plates, an amplifier after each |
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Module
import SquigglyLine.Style

namespace SquigglyLine

/-! ### Types -/

/-- A stack of plates, given by the axis of each: `axes 0`, `axes 1`, ...
Python: `Callable[[int], Vector]`. -/
abbrev PlateAxes (Space : Type*) := ℕ → Space

/-- The light after 0 plates, after 1 plate, after 2 plates, ...
Python: `Callable[[int], Vector]`. -/
abbrev LightAfterEachPlate (Space : Type*) := ℕ → Space

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]
  {axis light : Space}

/-! ### A plate -/

/-- A polarizer plate: the shadow of the light on the axis of the plate.
Python: `dot(axis, light) * axis`. -/
noncomputable def PASS_THROUGH_PLATE
    (axis : Space)
    (light : Space) : Space :=
  inner ℝ axis light • axis                                        -- the overlap (a number) times the axis (a direction)

/-- **Malus's law.** The shadow is as long as the overlap with the axis. -/
theorem norm_plate
    (axis_has_length_one : ‖axis‖ = 1)
    (light : Space) :
    let strength_after_plate := ‖PASS_THROUGH_PLATE axis light‖
    let size_of_overlap      := |inner ℝ axis light|               -- for light of strength 1 this is `|cos(angle to the axis)|`
    strength_after_plate = size_of_overlap := by
  unfold_named_pieces
  rw [PASS_THROUGH_PLATE, norm_smul, axis_has_length_one, mul_one,
    Real.norm_eq_abs]

/-- **Crossed plates block.** -/
theorem plate_of_crossed
    (light_is_crossed : inner ℝ axis light = 0) :                  -- no overlap: the light is at a right angle to the axis
    let light_after_plate := PASS_THROUGH_PLATE axis light
    light_after_plate = 0 := by
  unfold_named_pieces
  rw [PASS_THROUGH_PLATE, light_is_crossed, zero_smul]

/-! ### A skip connection: a plate with a bypass -/

/-- A plate with a bypass: the light that went around is added to the light
that went through.
Python: `light + PASS_THROUGH_PLATE(axis, light)`. -/
noncomputable def PASS_THROUGH_SKIP_PLATE
    (axis : Space)
    (light : Space) : Space :=
  light + PASS_THROUGH_PLATE axis light

/-- **A crossed plate with a bypass does nothing.** -/
theorem skipPlate_of_crossed
    (light_is_crossed : inner ℝ axis light = 0) :
    let light_after_plate := PASS_THROUGH_SKIP_PLATE axis light
    light_after_plate = light := by                                -- nothing goes through, so only the bypassed light is left
  unfold_named_pieces
  rw [PASS_THROUGH_SKIP_PLATE, plate_of_crossed light_is_crossed, add_zero]

/-- The squared length after a plate with a bypass. -/
theorem norm_skipPlate_sq
    (axis_has_length_one : ‖axis‖ = 1)
    (light : Space) :
    let overlap                 := inner ℝ axis light
    let squared_strength_before := ‖light‖ ^ 2
    let squared_strength_after  :=
      ‖PASS_THROUGH_SKIP_PLATE axis light‖ ^ 2
    squared_strength_after
      = squared_strength_before + 3 * overlap ^ 2 := by            -- the part along the axis doubles: `2 ^ 2 - 1 ^ 2 = 3`
  unfold_named_pieces
  have overlap_is_symmetric : inner ℝ light axis = inner ℝ axis light :=
    real_inner_comm _ _
  rw [PASS_THROUGH_SKIP_PLATE, PASS_THROUGH_PLATE, norm_add_sq_real,
    real_inner_smul_right, overlap_is_symmetric, norm_smul, mul_pow,
    axis_has_length_one, Real.norm_eq_abs, sq_abs]
  ring

/-- **A plate with a bypass never dims the light.** -/
theorem norm_le_norm_skipPlate
    (axis_has_length_one : ‖axis‖ = 1)
    (light : Space) :
    let strength_before := ‖light‖
    let strength_after  := ‖PASS_THROUGH_SKIP_PLATE axis light‖
    strength_before ≤ strength_after := by
  unfold_named_pieces
  -- Compare the squares: the square after is the square before plus
  -- something that is not negative.
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [norm_skipPlate_sq axis_has_length_one]
  nlinarith [sq_nonneg (inner ℝ axis light)]

/-- **The part along the axis doubles.** -/
theorem inner_skipPlate
    (axis_has_length_one : ‖axis‖ = 1)
    (light : Space) :
    let overlap_before := inner ℝ axis light
    let overlap_after  :=
      inner ℝ axis (PASS_THROUGH_SKIP_PLATE axis light)
    overlap_after = 2 * overlap_before := by                       -- once from the bypass, once through the plate
  unfold_named_pieces
  rw [PASS_THROUGH_SKIP_PLATE, PASS_THROUGH_PLATE, inner_add_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq, axis_has_length_one]
  ring

/-- **The rest is left as it was.** -/
theorem skipPlate_sub_plate
    (axis_has_length_one : ‖axis‖ = 1)
    (light : Space) :
    let light_after          := PASS_THROUGH_SKIP_PLATE axis light
    let off_axis_part_before := light - PASS_THROUGH_PLATE axis light  -- the light minus its shadow on the axis
    let off_axis_part_after  :=
      light_after - PASS_THROUGH_PLATE axis light_after
    off_axis_part_after = off_axis_part_before := by
  unfold_named_pieces
  rw [PASS_THROUGH_PLATE, inner_skipPlate axis_has_length_one,
    PASS_THROUGH_SKIP_PLATE, PASS_THROUGH_PLATE]
  module

/-- After `plate_count` plates with a bypass on the same axis, the part along
the axis has grown `2 ^ plate_count` times. -/
theorem inner_iterate_skipPlate
    (axis_has_length_one : ‖axis‖ = 1)
    (light : Space)
    (plate_count : ℕ) :
    let overlap_before := inner ℝ axis light
    let light_after    :=
      (PASS_THROUGH_SKIP_PLATE axis)^[plate_count] light           -- `^[plate_count]`: the plate applied that many times
    let overlap_after  := inner ℝ axis light_after
    overlap_after = 2 ^ plate_count * overlap_before := by         -- doubled once at each plate
  unfold_named_pieces
  induction plate_count with
  | zero => simp
  | succ plates_so_far overlap_so_far =>
    rw [Function.iterate_succ_apply', inner_skipPlate axis_has_length_one,
      overlap_so_far, pow_succ]
    ring

/-- **Closer at every plate, never there.** After `plate_count` plates with a
bypass the part of the light off the axis is exactly what it was. -/
theorem iterate_skipPlate_sub_plate
    (axis_has_length_one : ‖axis‖ = 1)
    (light : Space)
    (plate_count : ℕ) :
    let light_after          :=
      (PASS_THROUGH_SKIP_PLATE axis)^[plate_count] light
    let off_axis_part_before := light - PASS_THROUGH_PLATE axis light
    let off_axis_part_after  :=
      light_after - PASS_THROUGH_PLATE axis light_after
    off_axis_part_after = off_axis_part_before := by               -- only the part along the axis grows: never fully aligned
  unfold_named_pieces
  induction plate_count with
  | zero => rfl
  | succ plates_so_far off_axis_part_so_far =>
    rw [Function.iterate_succ_apply',
      skipPlate_sub_plate axis_has_length_one, off_axis_part_so_far]

/-! ### Normalisation: an amplifier -/

/-- An amplifier that brings the light back to full strength.
Python: `light / norm(light)`. -/
noncomputable def RENORMALIZE
    (light : Space) : Space :=
  ‖light‖⁻¹ • light                                                -- `⁻¹`: one over. Dividing by the length makes the length 1

/-- **Full strength.** -/
theorem norm_renorm
    (light_is_not_zero : light ≠ 0) :                              -- there has to be some light to amplify
    let strength_after := ‖RENORMALIZE light‖
    strength_after = 1 := by
  unfold_named_pieces
  rw [RENORMALIZE, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr light_is_not_zero)]

/-- **Nothing in, nothing out.** -/
theorem renorm_zero :
    let no_light : Space := 0
    RENORMALIZE no_light = 0 := by
  unfold_named_pieces
  rw [RENORMALIZE, smul_zero]

/-- **A plate and an amplifier turn the light without loss.** For any turn
short of a right angle, the light comes out along the axis at full
strength. -/
theorem renorm_plate
    (axis_has_length_one : ‖axis‖ = 1)
    (turn_is_under_a_right_angle : 0 < inner ℝ axis light) :       -- a positive overlap: less than 90 degrees from the axis
    let light_after_plate     := PASS_THROUGH_PLATE axis light
    let light_after_amplifier := RENORMALIZE light_after_plate
    light_after_amplifier = axis := by
  unfold_named_pieces
  rw [RENORMALIZE, norm_plate axis_has_length_one,
    abs_of_pos turn_is_under_a_right_angle, PASS_THROUGH_PLATE,
    inv_smul_smul₀ turn_is_under_a_right_angle.ne']

/-- With any overlap at all, of either sign, the output has full strength. -/
theorem norm_renorm_plate
    (axis_has_length_one : ‖axis‖ = 1)
    (light_is_not_crossed : inner ℝ axis light ≠ 0) :
    let light_after_plate := PASS_THROUGH_PLATE axis light
    let strength_after    := ‖RENORMALIZE light_after_plate‖
    strength_after = 1 := by
  unfold_named_pieces
  refine norm_renorm ?_
  -- Some light gets through the plate, because the overlap is not zero.
  have some_light_gets_through : 0 < ‖PASS_THROUGH_PLATE axis light‖ := by
    rw [norm_plate axis_has_length_one]
    exact abs_pos.mpr light_is_not_crossed
  exact norm_pos_iff.mp some_light_gets_through

/-- **An amplifier cannot raise the dead.** After a crossed plate there is
nothing to amplify. -/
theorem renorm_plate_of_crossed
    (light_is_crossed : inner ℝ axis light = 0) :
    let light_after_plate     := PASS_THROUGH_PLATE axis light
    let light_after_amplifier := RENORMALIZE light_after_plate
    light_after_amplifier = 0 := by
  unfold_named_pieces
  rw [plate_of_crossed light_is_crossed, renorm_zero]

/-- A stack of plates with axes `axes 1, axes 2, …`, an amplifier after each,
lit by full-strength light along `axes 0`. The result is the light after each
number of plates.
Python: `light = axes[0]`, then for each plate in turn
`light = RENORMALIZE(PASS_THROUGH_PLATE(axes[k + 1], light))`. -/
noncomputable def PASS_THROUGH_NORMED_PLATES
    (axes : PlateAxes Space) : LightAfterEachPlate Space
  | 0 => axes 0
  | plate_count + 1 =>
    RENORMALIZE
      (PASS_THROUGH_PLATE (axes (plate_count + 1))
        (PASS_THROUGH_NORMED_PLATES axes plate_count))

/-- **With amplifiers the loss is gone.** If each plate is turned less than a
right angle from the last, the light comes out along the last axis at full
strength, whatever the sizes of the turns. -/
theorem throughNormedPlates_eq
    {axes : PlateAxes Space}
    (axes_have_length_one : ∀ plate_index, ‖axes plate_index‖ = 1)
    (each_turn_is_under_a_right_angle :
      ∀ plate_index,
        0 < inner ℝ (axes (plate_index + 1)) (axes plate_index))
    (plate_count : ℕ) :
    let light_after_plates := PASS_THROUGH_NORMED_PLATES axes plate_count
    let last_axis          := axes plate_count
    light_after_plates = last_axis := by
  unfold_named_pieces
  induction plate_count with
  | zero => rfl
  | succ plates_so_far light_so_far_is_on_axis =>
    -- The light arrives along the previous axis, so one more plate and
    -- amplifier turn it onto the next axis without loss.
    rw [PASS_THROUGH_NORMED_PLATES, light_so_far_is_on_axis,
      renorm_plate (axes_have_length_one _)
        (each_turn_is_under_a_right_angle plates_so_far)]

end SquigglyLine
