/-
ReLU as a polarizer with a wide opening.

In the plane, ReLU sends each point to the nearest point of the positive
quadrant. A layer that rotates and then applies ReLU (an `APPLY_FAN`)
therefore acts on a bird sitting on the edge of the quadrant like a polarizer
on light:

* turn by `angle ≤ 90°` : the bird is pressed back onto the edge and keeps
                          the fraction `cos(angle)` of its length (Malus's
                          law);
* turn by `angle ≥ 90°` : the bird is blocked.

So `layer_count` small turns keep `cos(angle) ^ layer_count`, and a half turn
split into `step_count` steps keeps at least `1 - PI ^ 2 / (2 * step_count)`,
which tends to 1. One big turn loses everything; many small ones lose almost
nothing. This is the three-polarizer effect.

| Name                 | Meaning                                           |
|----------------------|---------------------------------------------------|
| `PlanePoint`         | a point of the plane: a pair `(across, up)`       |
| `APPLY_RELU_TO_PAIR` | ReLU on both coordinates                          |
| `ROTATE`             | turn a point about the origin by an angle         |
| `APPLY_FAN`          | one layer: rotate, then ReLU                      |
| `PLACE_ON_EDGE`      | the bird: the point `(length, 0)`                 |

Theorems: `abs_sub_relu_le`, `relu2_nearest`, `fan_of_le_pi_div_two`,
`fan_of_pi_div_two_le`, `iterate_fan`, `one_sub_le_cos_pow`.

How to read the notation:

* `point.1` and `point.2` are the two coordinates of a point: across and up.
  Python: `point[0]` and `point[1]`.
* `max value 0` is ReLU. Python: `max(value, 0)`.
* Angles are in radians: `PI / 2` is 90° and `PI` is 180°.
* `layer^[layer_count]` is `layer` applied `layer_count` times, one after
  the other.
-/
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import SquigglyLine.Style

namespace SquigglyLine

open Real

/-! ## Types -/

/-- A point of the plane: how far across, and how far up.
Python: `tuple[float, float]`. -/
abbrev PlanePoint := ℝ × ℝ

/-! ## The layer: rotate, then ReLU -/

/-- ReLU on the plane: a negative coordinate becomes zero.
Python: `(max(point[0], 0), max(point[1], 0))`. -/
def APPLY_RELU_TO_PAIR
    (point : PlanePoint) : PlanePoint :=
  (max point.1 0, max point.2 0)

/-- Rotation of the plane about the origin, anticlockwise, by an angle.
Python: `(cos(angle) * across - sin(angle) * up,
sin(angle) * across + cos(angle) * up)`. -/
noncomputable def ROTATE
    (angle : ℝ)
    (point : PlanePoint) : PlanePoint :=
  let across := point.1
  let up     := point.2
  (cos angle * across - sin angle * up,  -- the rotation formula from trigonometry
   sin angle * across + cos angle * up)

/-- One layer of the wind tunnel: rotate, then ReLU.
Python: `APPLY_RELU_TO_PAIR(ROTATE(angle, point))`. -/
noncomputable def APPLY_FAN
    (angle : ℝ)
    (point : PlanePoint) : PlanePoint :=
  APPLY_RELU_TO_PAIR (ROTATE angle point)

/-! ## ReLU sends a point to the nearest point of the quadrant -/

/-- On the number line, ReLU moves a number to the nearest number that is not
negative: no other such number is closer. -/
theorem abs_sub_relu_le
    (value : ℝ)
    {candidate : ℝ}
    (candidate_nonneg : 0 ≤ candidate) :
    let relu_output           := max value 0
    let distance_to_relu      := |value - relu_output|
    let distance_to_candidate := |value - candidate|
    distance_to_relu ≤ distance_to_candidate := by
  unfold_named_pieces
  rcases le_total 0 value with value_nonneg | value_nonpos
  · -- ReLU does not move a number that is not negative: the distance is 0.
    simp [max_eq_left value_nonneg]
  · -- ReLU moves a negative number to 0, and the candidate is beyond 0.
    rw [max_eq_right value_nonpos, sub_zero, abs_of_nonpos value_nonpos,
      abs_of_nonpos (by linarith)]
    linarith

/-- **ReLU is a projection.** It sends a point to the nearest point of the
positive quadrant: no other point of the quadrant is closer. -/
theorem relu2_nearest
    (point : PlanePoint)
    (candidate : PlanePoint)
    (candidate_across_nonneg : 0 ≤ candidate.1)
    (candidate_up_nonneg : 0 ≤ candidate.2) :
    let relu_output := APPLY_RELU_TO_PAIR point
    let squared_distance_to_relu :=
      (point.1 - relu_output.1) ^ 2 + (point.2 - relu_output.2) ^ 2  -- Pythagoras, without the square root
    let squared_distance_to_candidate :=
      (point.1 - candidate.1) ^ 2 + (point.2 - candidate.2) ^ 2      -- smaller squares mean smaller distances
    squared_distance_to_relu ≤ squared_distance_to_candidate := by
  unfold_named_pieces
  -- ReLU is nearest in each coordinate on its own, so it is nearest overall.
  exact add_le_add
    (sq_le_sq.mpr (abs_sub_relu_le point.1 candidate_across_nonneg))
    (sq_le_sq.mpr (abs_sub_relu_le point.2 candidate_up_nonneg))

/-! ## A bird on the edge of the quadrant

The bird is the point `(length, 0)`: on the edge of the quadrant, pointing
across. Each layer turns it clockwise by `angle`, out of the quadrant, and
ReLU presses it back. -/

/-- A bird of a given length sitting on the edge of the quadrant, pointing
across.
Python: `(length, 0.0)`. -/
abbrev PLACE_ON_EDGE
    (length : ℝ) : PlanePoint :=
  (length, 0)

-- Given, for the theorems below: the length of the bird and the angle of
-- one turn.
variable
  {length : ℝ}
  {angle : ℝ}

/-- **Malus's law.** A bird on the edge, turned out of the quadrant by at
most 90°, is pressed back onto the edge and keeps the fraction `cos(angle)`
of its length. -/
theorem fan_of_le_pi_div_two
    (length_nonneg : 0 ≤ length)
    (angle_nonneg : 0 ≤ angle)
    (angle_le_quarter_turn : angle ≤ PI / 2) :                  -- PI / 2 is 90°
    let bird_on_edge     := PLACE_ON_EDGE length
    let bird_after_layer := APPLY_FAN (-angle) bird_on_edge     -- minus: the turn is clockwise, out of the quadrant
    let kept_fraction    := cos angle                           -- the shadow of the turned bird on the edge
    let shorter_bird     := PLACE_ON_EDGE (length * kept_fraction)  -- back on the edge, only shorter
    bird_after_layer = shorter_bird := by
  unfold_named_pieces
  have cosine_nonneg : 0 ≤ cos angle :=
    cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], angle_le_quarter_turn⟩
  have sine_nonneg : 0 ≤ sin angle :=
    sin_nonneg_of_nonneg_of_le_pi angle_nonneg (by linarith [pi_pos])
  ext
  · -- Across: the turned bird has `length * cos angle`, which is not
    -- negative, so ReLU keeps it.
    show max (cos (-angle) * length - sin (-angle) * 0) 0
      = length * cos angle
    rw [cos_neg, mul_zero, sub_zero,
      max_eq_left (mul_nonneg cosine_nonneg length_nonneg), mul_comm]
  · -- Up: the turned bird has `-(sin angle) * length`, which is not
    -- positive, so ReLU makes it zero.
    show max (sin (-angle) * length + cos (-angle) * 0) 0 = 0
    rw [sin_neg, mul_zero, add_zero, max_eq_right]
    nlinarith [mul_nonneg sine_nonneg length_nonneg]

/-- **Crossed polarizers.** A bird turned by between 90° and 180° in one step
is blocked. -/
theorem fan_of_pi_div_two_le
    (length_nonneg : 0 ≤ length)
    (quarter_turn_le_angle : PI / 2 ≤ angle)                    -- PI / 2 is 90°
    (angle_le_half_turn : angle ≤ PI) :                         -- PI is 180°
    let bird_on_edge     := PLACE_ON_EDGE length
    let bird_after_layer := APPLY_FAN (-angle) bird_on_edge     -- minus: the turn is clockwise, out of the quadrant
    let nothing_left : PlanePoint := (0, 0)
    bird_after_layer = nothing_left := by
  unfold_named_pieces
  have cosine_nonpos : cos angle ≤ 0 :=
    cos_nonpos_of_pi_div_two_le_of_le quarter_turn_le_angle
      (by linarith [pi_pos])
  have sine_nonneg : 0 ≤ sin angle :=
    sin_nonneg_of_nonneg_of_le_pi (by linarith [pi_pos]) angle_le_half_turn
  ext
  · -- Across: past 90° the turned bird points backwards, so ReLU makes this
    -- coordinate zero.
    show max (cos (-angle) * length - sin (-angle) * 0) 0 = 0
    rw [cos_neg, mul_zero, sub_zero,
      max_eq_right
        (mul_nonpos_of_nonpos_of_nonneg cosine_nonpos length_nonneg)]
  · -- Up: the turned bird points downwards, so ReLU makes this one zero too.
    show max (sin (-angle) * length + cos (-angle) * 0) 0 = 0
    rw [sin_neg, mul_zero, add_zero, max_eq_right]
    nlinarith [mul_nonneg sine_nonneg length_nonneg]

/-- **Many small turns.** `layer_count` layers, each turning by at most 90°,
keep the fraction `cos(angle) ^ layer_count` of the length. -/
theorem iterate_fan
    (length_nonneg : 0 ≤ length)
    (angle_nonneg : 0 ≤ angle)
    (angle_le_quarter_turn : angle ≤ PI / 2)                    -- PI / 2 is 90°
    (layer_count : ℕ) :
    let bird_on_edge      := PLACE_ON_EDGE length
    let layer             := APPLY_FAN (-angle)
    let bird_after_layers := layer^[layer_count] bird_on_edge   -- `^[layer_count]`: the layer, applied that many times
    let kept_fraction     := cos angle ^ layer_count            -- Malus's law, once per layer
    let shorter_bird      := PLACE_ON_EDGE (length * kept_fraction)
    bird_after_layers = shorter_bird := by
  unfold_named_pieces
  have cosine_nonneg : 0 ≤ cos angle :=
    cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], angle_le_quarter_turn⟩
  induction layer_count with
  | zero => simp
  | succ earlier_layer_count bird_after_earlier_layers =>
    -- After the earlier layers the bird is on the edge again, only shorter.
    -- So Malus's law applies to the last layer as well.
    rw [Function.iterate_succ_apply', bird_after_earlier_layers,
      fan_of_le_pi_div_two
        (mul_nonneg length_nonneg
          (pow_nonneg cosine_nonneg earlier_layer_count))
        angle_nonneg angle_le_quarter_turn,
      pow_succ, mul_assoc]

/-- **The three-polarizer effect.** A half turn split into `step_count ≥ 3`
equal steps keeps at least `1 - PI ^ 2 / (2 * step_count)` of the length.
Split into one step it keeps nothing. -/
theorem one_sub_le_cos_pow
    {step_count : ℕ}
    (at_least_three_steps : 3 ≤ step_count) :                   -- then each step is at most 60°, small enough for the bound
    let step_angle    := PI / step_count                        -- a half turn is PI, cut into equal steps
    let kept_fraction := cos step_angle ^ step_count            -- Malus's law, once per step
    let lower_bound   := 1 - PI ^ 2 / (2 * step_count)          -- each step loses at most step_angle ^ 2 / 2, and the losses add up
    lower_bound ≤ kept_fraction := by
  unfold_named_pieces
  have three_le_step_count : (3 : ℝ) ≤ step_count := by
    exact_mod_cast at_least_three_steps
  have step_count_pos : (0 : ℝ) < step_count := by linarith
  set step_angle := PI / step_count with step_angle_def
  have step_angle_nonneg : 0 ≤ step_angle :=
    div_nonneg pi_pos.le step_count_pos.le
  have step_angle_is_small : step_angle ≤ 1.05 := by  -- PI / 3 = 1.047...
    rw [step_angle_def, div_le_iff₀ step_count_pos]
    nlinarith [pi_lt_d2]
  have one_step_keeps_something : 0 ≤ 1 - step_angle ^ 2 / 2 := by nlinarith
  -- One step keeps `cos step_angle ≥ 1 - step_angle ^ 2 / 2`. Bernoulli's
  -- inequality `(1 - loss) ^ count ≥ 1 - count * loss` then adds up the losses.
  calc 1 - PI ^ 2 / (2 * step_count)
      = 1 + step_count * (-(step_angle ^ 2 / 2)) := by
        rw [step_angle_def]; field_simp; ring
    _ ≤ (1 + -(step_angle ^ 2 / 2)) ^ step_count :=
        one_add_mul_le_pow (by nlinarith) step_count
    _ ≤ cos step_angle ^ step_count :=
        pow_le_pow_left₀ (by linarith)
          (by linarith [one_sub_sq_div_two_le_cos (x := step_angle)])
          step_count

end SquigglyLine
