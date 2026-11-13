/-
Depth multiplies the turns.

`APPLY_TENT` is one layer with two neurons. It folds the interval `[0, 1]` in
half: up from 0 to 1, then down from 1 to 0.

Stack `layer_count` of these layers. On the grid of `2 ^ layer_count + 1`
evenly spaced inputs the output alternates 0, 1, 0, 1, ... : zero at the even
grid points and one at the odd ones. So `2 * layer_count` neurons draw
`2 ^ layer_count` straight pieces and turn `2 ^ layer_count - 1` times. Each
layer folds everything the earlier layers made.

This is the precise form of "deeper allows more squiggliness". With one neuron
per layer the count stays at zero (`NarrowChain.lean`).

| Name                  | Meaning                                         |
|-----------------------|-------------------------------------------------|
| `APPLY_TENT`          | one layer: `2 * relu(x) - 4 * relu(x - 1/2)`    |
| `tent_of_le_half`     | on `[0, 1/2]` the tent is `2 * x`               |
| `tent_of_half_le`     | from `1/2` on the tent is `2 - 2 * x`           |
| `iterate_tent_dyadic` | stacked tents zigzag between 0 and 1 on the grid|

How to read the notation:

* `max value 0` is ReLU. Python: `max(value, 0)`.
* `APPLY_TENT^[layer_count]` is `APPLY_TENT` applied `layer_count` times, one
  after the other: a network that many layers deep.
-/
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.IntervalCases
import SquigglyLine.Style

namespace SquigglyLine

/-- One layer with two neurons: the tent `2 relu(x) - 4 relu(x - 1/2)`.
Python: `2 * max(input, 0) - 4 * max(input - 1 / 2, 0)`. -/
noncomputable def APPLY_TENT
    (input : ℝ) : ℝ :=
  let first_neuron  := max input 0            -- ReLU: zero until the input passes 0
  let second_neuron := max (input - 1 / 2) 0  -- ReLU: zero until the input passes the fold at 1/2
  2 * first_neuron - 4 * second_neuron        -- slope 2 before the fold, and 2 - 4 = -2 after it

/-- Left of the fold the tent rises: it doubles its input. -/
theorem tent_of_le_half
    {input : ℝ}
    (input_nonneg : 0 ≤ input)
    (input_le_half : input ≤ 1 / 2) :
    let tent_output := APPLY_TENT input
    let rising_line := 2 * input  -- only the first neuron is on, and it has slope 2
    tent_output = rising_line := by
  unfold_named_pieces
  -- The first neuron is on and the second one is off.
  show 2 * max input 0 - 4 * max (input - 1 / 2) 0 = 2 * input
  rw [max_eq_left input_nonneg, max_eq_right (by linarith)]
  ring

/-- Right of the fold the tent falls: from 1 at the fold back to 0 at 1. -/
theorem tent_of_half_le
    {input : ℝ}
    (half_le_input : 1 / 2 ≤ input) :
    let tent_output  := APPLY_TENT input
    let falling_line := 2 - 2 * input  -- both neurons on: 2 * x - 4 * (x - 1/2) = 2 - 2 * x
    tent_output = falling_line := by
  unfold_named_pieces
  -- Both neurons are on.
  show 2 * max input 0 - 4 * max (input - 1 / 2) 0 = 2 - 2 * input
  rw [max_eq_left (by linarith), max_eq_left (by linarith)]
  ring

/-- **Depth doubles the turns.** `layer_count` tent layers send grid point
number `grid_index`, of `2 ^ layer_count + 1` evenly spaced inputs, to 0 when
`grid_index` is even and to 1 when it is odd. -/
theorem iterate_tent_dyadic
    (layer_count : ℕ)
    (grid_index : ℕ)
    (index_is_on_grid : grid_index ≤ 2 ^ layer_count) :
    let grid_point : ℝ := (grid_index : ℝ) / 2 ^ layer_count    -- the grid cuts [0, 1] into 2 ^ layer_count equal steps
    let network_output := APPLY_TENT^[layer_count] grid_point   -- `^[layer_count]`: the tent, applied that many times
    let zigzag_value : ℝ := if Even grid_index then 0 else 1    -- 0, 1, 0, 1, ... along the grid
    network_output = zigzag_value := by
  unfold_named_pieces
  induction layer_count generalizing grid_index with
  | zero =>
    -- No layers: the grid is just 0 and 1, and the output is the input.
    simp only [pow_zero] at index_is_on_grid
    interval_cases grid_index <;> simp
  | succ layer_count zigzag_on_coarser_grid =>
    -- The first layer folds the fine grid onto the grid with half as many
    -- steps. The other layers then zigzag on that coarser grid.
    rw [Function.iterate_succ_apply]
    have coarse_step_count_pos : (0 : ℝ) < 2 ^ layer_count := by positivity
    rcases le_total grid_index (2 ^ layer_count) with
      index_in_left_half | index_in_right_half
    · -- Left half: the tent doubles the input, so the grid point keeps its
      -- number on the coarser grid.
      have index_le_half : (grid_index : ℝ) ≤ 2 ^ layer_count := by
        exact_mod_cast index_in_left_half
      have point_le_half :
          (grid_index : ℝ) / 2 ^ (layer_count + 1) ≤ 1 / 2 := by
        rw [pow_succ, div_le_iff₀ (by positivity)]
        linarith
      have first_layer_output :
          APPLY_TENT ((grid_index : ℝ) / 2 ^ (layer_count + 1))
            = (grid_index : ℝ) / 2 ^ layer_count := by
        rw [tent_of_le_half (by positivity) point_le_half, pow_succ]
        field_simp
      rw [first_layer_output,
        zigzag_on_coarser_grid grid_index index_in_left_half]
    · -- Right half: the tent mirrors the input, so the grid point gets the
      -- mirrored number. Mirroring keeps even numbers even and odd ones odd.
      have half_le_index : (2 : ℝ) ^ layer_count ≤ grid_index := by
        exact_mod_cast index_in_right_half
      have mirrored_index_is_on_grid :
          2 ^ (layer_count + 1) - grid_index ≤ 2 ^ layer_count := by
        rw [pow_succ]
        omega
      have half_le_point :
          1 / 2 ≤ (grid_index : ℝ) / 2 ^ (layer_count + 1) := by
        rw [pow_succ, le_div_iff₀ (by positivity)]
        linarith
      have first_layer_output :
          APPLY_TENT ((grid_index : ℝ) / 2 ^ (layer_count + 1))
            = ((2 ^ (layer_count + 1) - grid_index : ℕ) : ℝ)
              / 2 ^ layer_count := by
        rw [tent_of_half_le half_le_point, Nat.cast_sub index_is_on_grid]
        push_cast
        rw [pow_succ]
        field_simp
      have mirroring_keeps_evenness :
          Even (2 ^ (layer_count + 1) - grid_index) ↔ Even grid_index := by
        rw [Nat.even_sub index_is_on_grid]
        simp [Nat.even_pow]
      rw [first_layer_output,
        zigzag_on_coarser_grid _ mirrored_index_is_on_grid]
      simp only [mirroring_keeps_evenness]

end SquigglyLine
