/-
Three polarizers, and the photon's squiggly line.

`MAKE_LIGHT amplitude light_angle` is an arrow of length `amplitude` pointing
at angle `light_angle`: light of strength `amplitude` vibrating along that
direction. `PASS_THROUGH_POLARIZER axis_angle` replaces an arrow by its shadow
on the direction `axis_angle`.

* `malus`: the shadow has length `amplitude * cos(axis_angle - light_angle)`
  and points along `axis_angle`.
* `polarizer_crossed`: a plate at 90° to the arrow blocks it.
* `throughPlates_light`: after `plate_count` plates, each turned by
  `turn_angle` from the last, the arrow has length
  `amplitude * cos(turn_angle) ^ plate_count` and angle
  `plate_count * turn_angle`. The tips of these arrows are the photon's
  squiggly line.
* `three_polarizers`: a plate at 45° and then one at 90° pass half the
  length, where the 90° plate alone passes none.
* `quarter_turn_arrives`: a quarter turn in `plate_count ≥ 2` plates delivers
  at least `1 - PI ^ 2 / (8 * plate_count)` of the length. More plates, a
  squigglier path, a closer end.

| Name                     | Meaning                                       |
|--------------------------|-----------------------------------------------|
| `LightArrow`             | an arrow in the plane: a pair `(across, up)`  |
| `NO_LIGHT`               | the arrow of length zero                      |
| `MAKE_LIGHT`             | the arrow with a given length and angle       |
| `PASS_THROUGH_POLARIZER` | the shadow of an arrow on one direction       |
| `PASS_THROUGH_PLATES`    | several polarizers in a row, each turned more |

How to read the notation:

* `arrow.1` and `arrow.2` are the two parts of an arrow: across and up.
  Python: `arrow[0]` and `arrow[1]`.
* Angles are in radians: `PI / 4` is 45° and `PI / 2` is 90°. Angle 0 points
  across and angle `PI / 2` points straight up.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import SquigglyLine.Style

namespace SquigglyLine

open Real

/-! ## Types -/

/-- An arrow in the plane: how far it reaches across, and how far up.
Python: `tuple[float, float]`. -/
abbrev LightArrow := ℝ × ℝ

/-- No light at all: the arrow of length zero.
Python: `(0.0, 0.0)`. -/
abbrev NO_LIGHT : LightArrow := (0, 0)

/-! ## Light and one polarizer -/

/-- An arrow of length `amplitude` at angle `light_angle`: light of strength
`amplitude` vibrating along that direction.
Python: `(amplitude * cos(light_angle), amplitude * sin(light_angle))`. -/
noncomputable def MAKE_LIGHT
    (amplitude : ℝ)
    (light_angle : ℝ) : LightArrow :=
  (amplitude * cos light_angle, amplitude * sin light_angle)  -- the two sides of a right triangle with the arrow as its long side

/-- A polarizer with its axis at angle `axis_angle`: the shadow of the arrow
on that direction.

    def PASS_THROUGH_POLARIZER(axis_angle, arrow):
        shadow_length = (
            arrow[0] * cos(axis_angle) + arrow[1] * sin(axis_angle))
        return MAKE_LIGHT(shadow_length, axis_angle)
-/
noncomputable def PASS_THROUGH_POLARIZER
    (axis_angle : ℝ)
    (arrow : LightArrow) : LightArrow :=
  let shadow_length :=
    arrow.1 * cos axis_angle + arrow.2 * sin axis_angle           -- the dot product of the arrow with the axis direction
  (shadow_length * cos axis_angle, shadow_length * sin axis_angle)  -- an arrow of that length, laid along the axis

/-- **Malus's law.** The shadow has `cos` of the angle between arrow and
axis. -/
theorem malus
    (amplitude : ℝ)
    (light_angle : ℝ)
    (axis_angle : ℝ) :
    let incoming_light := MAKE_LIGHT amplitude light_angle
    let outgoing_light := PASS_THROUGH_POLARIZER axis_angle incoming_light
    let kept_fraction  := cos (axis_angle - light_angle)                    -- the angle between the arrow and the axis
    let shadow         := MAKE_LIGHT (amplitude * kept_fraction) axis_angle  -- shorter, and now along the axis
    outgoing_light = shadow := by
  unfold_named_pieces
  -- Write both arrows out in coordinates. What is left is the formula for
  -- the cosine of a difference.
  ext <;> simp only [PASS_THROUGH_POLARIZER, MAKE_LIGHT, cos_sub] <;> ring

/-- Light of strength zero is no light, whatever its direction. -/
theorem light_zero
    (light_angle : ℝ) :
    let light_of_strength_zero := MAKE_LIGHT 0 light_angle
    light_of_strength_zero = NO_LIGHT := by
  unfold_named_pieces
  simp [MAKE_LIGHT]

/-- **Crossed plates block.** A polarizer at 90° to the light lets nothing
through. -/
theorem polarizer_crossed
    (amplitude : ℝ)
    (light_angle : ℝ) :
    let incoming_light := MAKE_LIGHT amplitude light_angle
    let crossed_axis   := light_angle + PI / 2  -- PI / 2 is 90°: at right angles to the light
    let outgoing_light := PASS_THROUGH_POLARIZER crossed_axis incoming_light
    outgoing_light = NO_LIGHT := by
  unfold_named_pieces
  -- By Malus's law the light keeps `cos (PI / 2)` of its length, which is 0.
  rw [malus, add_sub_cancel_left, cos_pi_div_two, mul_zero, light_zero]

/-! ## Many polarizers in a row -/

/-- A stack of `plate_count` plates. Plate number `j`, counting from 1, has
its axis at `j * turn_angle`.

    def PASS_THROUGH_PLATES(turn_angle, plate_count, arrow):
        for plate_number in range(1, plate_count + 1):
            arrow = PASS_THROUGH_POLARIZER(plate_number * turn_angle, arrow)
        return arrow
-/
noncomputable def PASS_THROUGH_PLATES
    (turn_angle : ℝ)
    (plate_count : ℕ)
    (arrow : LightArrow) : LightArrow :=
  match plate_count, arrow with
  | 0, arrow => arrow  -- no plates: the light is unchanged
  | earlier_plate_count + 1, arrow =>
    let last_plate_number : ℕ := earlier_plate_count + 1
    let last_axis_angle := (last_plate_number : ℝ) * turn_angle  -- each plate is turned by turn_angle from the one before
    let light_before_last_plate :=
      PASS_THROUGH_PLATES turn_angle earlier_plate_count arrow
    PASS_THROUGH_POLARIZER last_axis_angle light_before_last_plate

/-- **The photon's path.** After `plate_count` plates the arrow has length
`amplitude * cos(turn_angle) ^ plate_count` and angle
`plate_count * turn_angle`. -/
theorem throughPlates_light
    (amplitude : ℝ)
    (turn_angle : ℝ)
    (plate_count : ℕ) :
    let incoming_light := MAKE_LIGHT amplitude 0             -- angle 0: pointing across
    let outgoing_light :=
      PASS_THROUGH_PLATES turn_angle plate_count incoming_light
    let kept_fraction  := cos turn_angle ^ plate_count       -- Malus's law, once per plate
    let final_angle    := plate_count * turn_angle           -- the light leaves along the axis of the last plate
    let expected_light :=
      MAKE_LIGHT (amplitude * kept_fraction) final_angle
    outgoing_light = expected_light := by
  unfold_named_pieces
  induction plate_count with
  | zero => simp [PASS_THROUGH_PLATES]
  | succ earlier_plate_count light_before_last_plate =>
    -- Peel off the last plate. The light reaches it at an angle of
    -- `turn_angle` to its axis, so Malus's law gives one more factor.
    rw [PASS_THROUGH_PLATES, light_before_last_plate, malus,
      show ((earlier_plate_count + 1 : ℕ) : ℝ) * turn_angle
          - earlier_plate_count * turn_angle = turn_angle by
        push_cast; ring,
      pow_succ, mul_assoc]

/-- **Three polarizers.** With a plate at 45° in between, half the length
reaches the vertical. -/
theorem three_polarizers :
    let incoming_light := MAKE_LIGHT 1 0                     -- strength 1, pointing across
    let turn_angle     := PI / 4                             -- 45°: the first plate is at 45° and the second at 90°
    let outgoing_light :=
      PASS_THROUGH_PLATES turn_angle 2 incoming_light
    let half_pointing_up : LightArrow := (0, 1 / 2)          -- cos(45°) ^ 2 = 1/2, once for each plate
    outgoing_light = half_pointing_up := by
  unfold_named_pieces
  rw [throughPlates_light, MAKE_LIGHT, one_mul, cos_pi_div_four,
    show ((2 : ℕ) : ℝ) * (PI / 4) = PI / 2 by push_cast; ring,
    cos_pi_div_two, sin_pi_div_two, mul_zero, mul_one, div_pow,
    sq_sqrt (by norm_num)]
  norm_num

/-- Without the plate in between, nothing reaches the vertical. -/
theorem two_polarizers :
    let incoming_light := MAKE_LIGHT 1 0                     -- strength 1, pointing across
    let vertical_axis  := PI / 2                             -- 90°: at right angles to the light
    let outgoing_light :=
      PASS_THROUGH_POLARIZER vertical_axis incoming_light
    outgoing_light = NO_LIGHT := by
  unfold_named_pieces
  simpa using polarizer_crossed 1 0

/-! ## More plates lose less -/

/-- A small turn loses little: `cos(turn_angle) ^ plate_count` is at least
`1 - plate_count * (turn_angle ^ 2 / 2)`. -/
theorem one_sub_mul_le_cos_pow
    {turn_angle : ℝ}
    (turn_is_small : turn_angle ^ 2 ≤ 2)                     -- so that one plate cannot lose more than everything
    (plate_count : ℕ) :
    let loss_per_plate : ℝ := turn_angle ^ 2 / 2             -- because cos(x) ≥ 1 - x ^ 2 / 2
    let kept_fraction  := cos turn_angle ^ plate_count       -- Malus's law, once per plate
    let lower_bound    := 1 - plate_count * loss_per_plate   -- at worst the losses add up
    lower_bound ≤ kept_fraction := by
  unfold_named_pieces
  -- One plate keeps `cos turn_angle ≥ 1 - turn_angle ^ 2 / 2`. Bernoulli's
  -- inequality `(1 - loss) ^ count ≥ 1 - count * loss` then adds up the losses.
  calc 1 - plate_count * (turn_angle ^ 2 / 2)
      = 1 + plate_count * (-(turn_angle ^ 2 / 2)) := by ring
    _ ≤ (1 + -(turn_angle ^ 2 / 2)) ^ plate_count :=
        one_add_mul_le_pow (by nlinarith [sq_nonneg turn_angle]) plate_count
    _ ≤ cos turn_angle ^ plate_count :=
        pow_le_pow_left₀ (by linarith)
          (by linarith [one_sub_sq_div_two_le_cos (x := turn_angle)])
          plate_count

/-- **More plates, closer.** A quarter turn in `plate_count ≥ 2` plates
arrives pointing straight up, with at least
`1 - PI ^ 2 / (8 * plate_count)` of its length. -/
theorem quarter_turn_arrives
    {plate_count : ℕ}
    (at_least_two_plates : 2 ≤ plate_count) :                -- then each plate turns by at most 45°, small enough for the bound
    let turn_angle     := PI / (2 * plate_count)             -- a quarter turn is PI / 2, cut into equal steps
    let incoming_light := MAKE_LIGHT 1 0                     -- strength 1, pointing across
    let outgoing_light :=
      PASS_THROUGH_PLATES turn_angle plate_count incoming_light
    let kept_fraction  := cos turn_angle ^ plate_count       -- Malus's law, once per plate
    let light_pointing_up : LightArrow := (0, kept_fraction)
    let lower_bound    := 1 - PI ^ 2 / (8 * plate_count)     -- plate_count * turn_angle ^ 2 / 2, worked out
    let arrives_pointing_up      := outgoing_light = light_pointing_up
    let keeps_most_of_its_length := lower_bound ≤ kept_fraction
    arrives_pointing_up ∧ keeps_most_of_its_length := by
  unfold_named_pieces
  have two_le_plate_count : (2 : ℝ) ≤ plate_count := by
    exact_mod_cast at_least_two_plates
  have plate_count_pos : (0 : ℝ) < plate_count := by linarith
  constructor
  · -- The last plate's axis is at `plate_count * turn_angle = PI / 2`:
    -- straight up.
    rw [throughPlates_light, MAKE_LIGHT, one_mul,
      show (plate_count : ℝ) * (PI / (2 * plate_count)) = PI / 2 by
        field_simp,
      cos_pi_div_two, sin_pi_div_two, mul_zero, mul_one]
  · have turn_angle_nonneg : 0 ≤ PI / (2 * plate_count) := by positivity
    have turn_angle_is_small : PI / (2 * plate_count) ≤ 0.7875 := by  -- PI / 4 = 0.785...
      rw [div_le_iff₀ (by positivity)]
      nlinarith [pi_lt_d2]
    have losses_add_up :=
      one_sub_mul_le_cos_pow (turn_angle := PI / (2 * plate_count))
        (by nlinarith) plate_count
    calc 1 - PI ^ 2 / (8 * plate_count)
        = 1 - plate_count * ((PI / (2 * plate_count)) ^ 2 / 2) := by
          field_simp; ring
      _ ≤ cos (PI / (2 * plate_count)) ^ plate_count := losses_add_up

end SquigglyLine
