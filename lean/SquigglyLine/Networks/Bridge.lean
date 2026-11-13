/-
The bridge, part 1: a fold is a frequency doubling.

Look at the output of the wind tunnel through the fixed lens
`sin² (PI/2 · y)`. One `APPLY_TENT` layer then doubles the angle inside the
sine:

    sin² (PI/2 · tent input) = sin² (PI · input)

and `layer_count` layers double it `layer_count` times:

    sin² (PI/2 · tent^[layer_count] input)
        = sin² (2 ^ layer_count · (PI/2 · input))

The right side is a single Fourier term, of frequency `2 ^ layer_count` once
the square is written as a cosine. So depth in the ReLU model is the
logarithm of frequency in the Fourier model.

Theorems:

* `tent_mem_Icc`            one tent layer keeps `[0, 1]` inside `[0, 1]`;
* `iterate_tent_mem_Icc`    so does a stack of them;
* `sin_sq_tent`             one fold doubles the angle;
* `sin_sq_two_mul`          the double-angle formula for `sin²`;
* `sin_sq_iterate_tent`     `layer_count` folds are one Fourier term of
                            frequency `2 ^ layer_count`.
-/
import SquigglyLine.Networks.Depth
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace SquigglyLine

open Real

variable {input : ℝ}

/-- One tent layer keeps the unit interval inside the unit interval. -/
theorem tent_mem_Icc
    (input_nonneg : 0 ≤ input)
    (input_le_one : input ≤ 1) :
    let tent_output := APPLY_TENT input
    let output_nonneg := 0 ≤ tent_output
    let output_le_one := tent_output ≤ 1
    output_nonneg ∧ output_le_one := by
  unfold_named_pieces
  rcases le_total input (1 / 2) with input_in_left_half | input_in_right_half
  · rw [tent_of_le_half input_nonneg input_in_left_half]
    constructor <;> linarith
  · rw [tent_of_half_le input_in_right_half]
    constructor <;> linarith

/-- The wind tunnel keeps the unit interval inside the unit interval. -/
theorem iterate_tent_mem_Icc
    (input_nonneg : 0 ≤ input)
    (input_le_one : input ≤ 1)
    (layer_count : ℕ) :
    let network_output := APPLY_TENT^[layer_count] input
    let output_nonneg := 0 ≤ network_output
    let output_le_one := network_output ≤ 1
    output_nonneg ∧ output_le_one := by
  unfold_named_pieces
  induction layer_count with
  | zero => exact ⟨input_nonneg, input_le_one⟩
  | succ layer_count output_in_unit_interval =>
    rw [Function.iterate_succ_apply']
    exact tent_mem_Icc output_in_unit_interval.1 output_in_unit_interval.2

/-- **One fold doubles the angle.** -/
theorem sin_sq_tent
    (input_nonneg : 0 ≤ input) :
    let folded_value  := sin (PI / 2 * APPLY_TENT input) ^ 2  -- the lens `sin² (PI/2 · y)` applied to one fold
    let doubled_value := sin (PI * input) ^ 2                 -- the angle `PI/2 · input` doubled
    folded_value = doubled_value := by
  unfold_named_pieces
  rcases le_total input (1 / 2) with input_in_left_half | input_in_right_half
  · -- Rising side: the tent doubles the input, so the angle doubles.
    rw [tent_of_le_half input_nonneg input_in_left_half,
      show PI / 2 * (2 * input) = PI * input by ring]
  · -- Falling side: the tent mirrors the input; `sin (PI - a) = sin a`.
    rw [tent_of_half_le input_in_right_half,
      show PI / 2 * (2 - 2 * input) = PI - PI * input by ring, sin_pi_sub]

/-- The double-angle formula for `sin²`. -/
theorem sin_sq_two_mul
    (angle : ℝ) :
    let doubled_angle_value := sin (2 * angle) ^ 2
    let polynomial_in_sin   := 4 * sin angle ^ 2 * (1 - sin angle ^ 2)  -- sin 2a = 2 sin a cos a, and cos² = 1 - sin²
    doubled_angle_value = polynomial_in_sin := by
  unfold_named_pieces
  rw [sin_two_mul, ← cos_sq']
  ring

/-- **`layer_count` folds are one Fourier term of frequency
`2 ^ layer_count`.** Seen through the lens `sin² (PI/2 · y)`, the wind tunnel
of depth `layer_count` is `sin²` of `2 ^ layer_count` times the input angle. -/
theorem sin_sq_iterate_tent
    (input_nonneg : 0 ≤ input)
    (input_le_one : input ≤ 1)
    (layer_count : ℕ) :
    let tunnel_value  := sin (PI / 2 * APPLY_TENT^[layer_count] input) ^ 2
    let fourier_value := sin (2 ^ layer_count * (PI / 2 * input)) ^ 2  -- each layer doubles the angle
    tunnel_value = fourier_value := by
  unfold_named_pieces
  induction layer_count with
  | zero => simp
  | succ layer_count angle_doubled_so_far =>
    -- One more fold doubles the angle once more, by the double-angle formula.
    rw [Function.iterate_succ_apply',
      sin_sq_tent (iterate_tent_mem_Icc input_nonneg input_le_one layer_count).1,
      show PI * APPLY_TENT^[layer_count] input
        = 2 * (PI / 2 * APPLY_TENT^[layer_count] input) by ring,
      show (2 : ℝ) ^ (layer_count + 1) * (PI / 2 * input)
        = 2 * (2 ^ layer_count * (PI / 2 * input)) by ring,
      sin_sq_two_mul, sin_sq_two_mul, angle_doubled_so_far]

end SquigglyLine
