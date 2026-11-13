/-
Depth separation: a shallow network pays one unit per turn.

* `affineOn_reluUnit` : a ReLU unit is a straight line on any stretch that
  does not contain its kink.
* `IS_AFFINE_ON.not_zigzag` : a straight line cannot be lower at both ends of
  a stretch than in the middle.
* `exists_kink_of_zigzag` : so if a one-hidden-layer network goes up and comes
  back down, some unit has its kink in between.
* `card_ge_of_zigzag` : a zigzag with `turn_count` ups and downs needs
  `turn_count` units.
* `depth_separation` : `layer_count + 1` tent layers (`2 (layer_count + 1)`
  neurons) draw a zigzag that no one-hidden-layer network with fewer than
  `2 ^ layer_count` units can follow, even to within one half at the grid
  points.

Definitions:

* `IS_AFFINE_ON`               a model is a straight line on a stretch;
* `EVALUATE_SHALLOW_NETWORK`   the value of a one-hidden-layer ReLU network.

Other lemmas: `IS_AFFINE_ON.const_mul`, `affineOn_sum` and
`exists_zero_between` are the small steps on the way.
-/
import Mathlib.Tactic.Choose
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination
import SquigglyLine.Networks.Depth

namespace SquigglyLine

/-! ### Straight lines -/

/-- `model` is a straight line on the set `stretch`.
Python: `all(model(x) == slope * x + intercept for x in stretch)` for some
`slope` and `intercept`. -/
def IS_AFFINE_ON
    (model : RealFunction)
    (stretch : Set ℝ) : Prop :=
  ∃ slope intercept : ℝ,
    ∀ input ∈ stretch, model input = slope * input + intercept

namespace IS_AFFINE_ON

variable {model : RealFunction} {stretch : Set ℝ}

/-- A multiple of a straight line is a straight line. -/
theorem const_mul
    (factor : ℝ)
    (is_line : IS_AFFINE_ON model stretch) :
    let scaled_is_line :=
      IS_AFFINE_ON (fun input => factor * model input) stretch
    scaled_is_line := by
  unfold_named_pieces
  obtain ⟨slope, intercept, line_formula⟩ := is_line
  refine ⟨factor * slope, factor * intercept, fun input input_in_stretch => ?_⟩
  show factor * model input = factor * slope * input + factor * intercept
  rw [line_formula input input_in_stretch]
  ring

/-- **A straight line cannot go up and come back down.** -/
theorem not_zigzag
    {left middle right : ℝ}
    (is_line : IS_AFFINE_ON model (Set.Icc left right))
    (left_lt_middle : left < middle)
    (middle_lt_right : middle < right)
    (left_below_middle : model left < model middle)
    (right_below_middle : model right < model middle) :
    False := by
  obtain ⟨slope, intercept, line_formula⟩ := is_line
  rw [line_formula left ⟨le_rfl, by linarith⟩,
    line_formula middle ⟨left_lt_middle.le, middle_lt_right.le⟩]
    at left_below_middle
  rw [line_formula right ⟨by linarith, le_rfl⟩,
    line_formula middle ⟨left_lt_middle.le, middle_lt_right.le⟩]
    at right_below_middle
  -- Lower on the left means the slope is positive ...
  have slope_pos : 0 < slope := by
    by_contra slope_nonpos
    push Not at slope_nonpos
    have drop_is_nonneg :=
      mul_nonneg (neg_nonneg.mpr slope_nonpos) (sub_pos.mpr left_lt_middle).le
    linarith
  -- ... which makes the right end higher than the middle.
  have rise_is_pos := mul_pos slope_pos (sub_pos.mpr middle_lt_right)
  linarith

end IS_AFFINE_ON

/-- A sum of straight lines is a straight line. -/
theorem affineOn_sum
    {Index : Type*}
    (indices : Finset Index)
    (summand : Index → RealFunction)
    {stretch : Set ℝ}
    (every_summand_is_line :
      ∀ j ∈ indices, IS_AFFINE_ON (summand j) stretch) :
    let sum_is_line :=
      IS_AFFINE_ON (fun input => ∑ j ∈ indices, summand j input) stretch
    sum_is_line := by
  unfold_named_pieces
  classical
  induction indices using Finset.induction_on with
  | empty => exact ⟨0, 0, fun input _ => by simp⟩
  | insert new_index rest new_index_not_in_rest rest_is_line =>
    obtain ⟨head_slope, head_intercept, head_formula⟩ :=
      every_summand_is_line new_index (Finset.mem_insert_self new_index rest)
    obtain ⟨rest_slope, rest_intercept, rest_formula⟩ :=
      rest_is_line (fun j j_in_rest =>
        every_summand_is_line j (Finset.mem_insert_of_mem j_in_rest))
    refine ⟨head_slope + rest_slope, head_intercept + rest_intercept,
      fun input input_in_stretch => ?_⟩
    have rest_sum_formula :
        ∑ j ∈ rest, summand j input = rest_slope * input + rest_intercept :=
      rest_formula input input_in_stretch
    show ∑ j ∈ insert new_index rest, summand j input
      = (head_slope + rest_slope) * input + (head_intercept + rest_intercept)
    rw [Finset.sum_insert new_index_not_in_rest,
      head_formula input input_in_stretch, rest_sum_formula]
    ring

/-! ### One ReLU unit bends once -/

/-- A line that is below zero at `input` and above zero at `middle` is zero
somewhere strictly inside any stretch that holds `input` and has `middle` in
its interior. -/
theorem exists_zero_between
    {weight bias left right input middle : ℝ}
    (left_le_input : left ≤ input)
    (input_le_right : input ≤ right)
    (left_lt_middle : left < middle)
    (middle_lt_right : middle < right)
    (line_negative_at_input : weight * input + bias < 0)
    (line_positive_at_middle : 0 < weight * middle + bias) :
    let is_after_left   := fun (crossing : ℝ) => left < crossing
    let is_before_right := fun (crossing : ℝ) => crossing < right
    let is_zero_of_line := fun (crossing : ℝ) => weight * crossing + bias = 0
    ∃ crossing, is_after_left crossing ∧ is_before_right crossing
      ∧ is_zero_of_line crossing := by
  unfold_named_pieces
  beta_reduce
  have gap_positive :
      0 < (weight * middle + bias) - (weight * input + bias) := by
    linarith
  -- How far along from `input` to `middle` the line reaches zero.
  obtain ⟨fraction, fraction_def⟩ :
      ∃ fraction, fraction = -(weight * input + bias)
        / ((weight * middle + bias) - (weight * input + bias)) :=
    ⟨_, rfl⟩
  have fraction_pos : 0 < fraction := by
    rw [fraction_def]
    exact div_pos (by linarith) gap_positive
  have fraction_lt_one : fraction < 1 := by
    rw [fraction_def, div_lt_one gap_positive]
    linarith
  have fraction_times_gap :
      fraction * ((weight * middle + bias) - (weight * input + bias))
        = -(weight * input + bias) := by
    rw [fraction_def, div_mul_cancel₀ _ gap_positive.ne']
  refine ⟨(1 - fraction) * input + fraction * middle, ?_, ?_, ?_⟩
  · have from_left :=
      mul_nonneg (sub_nonneg.mpr fraction_lt_one.le)
        (sub_nonneg.mpr left_le_input)
    have toward_middle := mul_pos fraction_pos (sub_pos.mpr left_lt_middle)
    nlinarith
  · have from_right :=
      mul_nonneg (sub_nonneg.mpr fraction_lt_one.le)
        (sub_nonneg.mpr input_le_right)
    have toward_middle := mul_pos fraction_pos (sub_pos.mpr middle_lt_right)
    nlinarith
  · linear_combination fraction_times_gap

/-- **A ReLU unit is straight away from its kink.** If `weight * point + bias`
is never zero strictly inside a stretch, the unit
`max (weight * input + bias) 0` is a straight line on the whole stretch. -/
theorem affineOn_reluUnit
    {weight bias left right : ℝ}
    (left_lt_right : left < right)
    (no_zero_inside :
      ∀ point, left < point → point < right → weight * point + bias ≠ 0) :
    let unit_is_line :=
      IS_AFFINE_ON (fun input => max (weight * input + bias) 0)
        (Set.Icc left right)
    unit_is_line := by
  unfold_named_pieces
  have left_lt_midpoint : left < (left + right) / 2 := by linarith
  have midpoint_lt_right : (left + right) / 2 < right := by linarith
  rcases lt_or_gt_of_ne
      (no_zero_inside _ left_lt_midpoint midpoint_lt_right) with
    line_negative_inside | line_positive_inside
  · -- The line is below zero inside, so the unit is off: the zero line.
    refine ⟨0, 0, fun input input_in_stretch => ?_⟩
    have line_nonpos : weight * input + bias ≤ 0 := by
      by_contra line_positive
      push Not at line_positive
      obtain ⟨crossing, after_left, before_right, crossing_is_zero⟩ :=
        exists_zero_between (weight := -weight) (bias := -bias)
          input_in_stretch.1 input_in_stretch.2 left_lt_midpoint
          midpoint_lt_right (by linarith) (by linarith)
      exact no_zero_inside crossing after_left before_right
        (by linarith)
    show max (weight * input + bias) 0 = 0 * input + 0
    rw [max_eq_right line_nonpos]
    ring
  · -- The line is above zero inside, so the unit is on: the line itself.
    refine ⟨weight, bias, fun input input_in_stretch => ?_⟩
    have line_nonneg : 0 ≤ weight * input + bias := by
      by_contra line_negative
      push Not at line_negative
      obtain ⟨crossing, after_left, before_right, crossing_is_zero⟩ :=
        exists_zero_between input_in_stretch.1 input_in_stretch.2
          left_lt_midpoint midpoint_lt_right line_negative line_positive_inside
      exact no_zero_inside crossing after_left before_right crossing_is_zero
    exact max_eq_left line_nonneg

/-! ### A network with one hidden layer -/

section Shallow

variable {Index : Type*}

/-- A network with one hidden layer of ReLU units, indexed by `units`: unit `j`
has input weight `unit_slope j`, bias `unit_bias j` and output weight
`unit_gain j`.
Python: `sum(gain[j] * max(slope[j] * input + bias[j], 0) for j in units)`. -/
noncomputable def EVALUATE_SHALLOW_NETWORK
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    (input : ℝ) : ℝ :=
  ∑ j ∈ units, unit_gain j * max (unit_slope j * input + unit_bias j) 0

/-- **Every up-and-down holds a kink.** If the network is lower at both ends of
a stretch than at a point inside it, some unit has its kink strictly inside the
stretch. -/
theorem exists_kink_of_zigzag
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    {left middle right : ℝ}
    (left_lt_middle : left < middle)
    (middle_lt_right : middle < right)
    (left_below_middle :
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias left
        < EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias middle)
    (right_below_middle :
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias right
        < EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          middle) :
    let is_after_left   := fun (crossing : ℝ) => left < crossing
    let is_before_right := fun (crossing : ℝ) => crossing < right
    let is_kink_of      := fun (unit : Index) (crossing : ℝ) =>
      unit_slope unit * crossing + unit_bias unit = 0  -- the unit switches on or off here
    let has_slope       := fun (unit : Index) => unit_slope unit ≠ 0
    let has_kink_inside := fun (unit : Index) =>
      ∃ crossing, is_after_left crossing ∧ is_before_right crossing
        ∧ is_kink_of unit crossing
    ∃ unit ∈ units, has_slope unit ∧ has_kink_inside unit := by
  unfold_named_pieces
  beta_reduce
  by_contra no_kink_inside
  push Not at no_kink_inside
  -- With no kink inside, every unit is straight on the stretch, and so is
  -- their sum. A straight line cannot zigzag.
  have network_is_line :
      IS_AFFINE_ON (EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope
        unit_bias) (Set.Icc left right) := by
    show IS_AFFINE_ON
      (fun input => ∑ j ∈ units,
        unit_gain j * max (unit_slope j * input + unit_bias j) 0)
      (Set.Icc left right)
    refine affineOn_sum units
      (fun j input => unit_gain j * max (unit_slope j * input + unit_bias j) 0)
      (fun j j_in_units => ?_)
    refine IS_AFFINE_ON.const_mul
      (model := fun input => max (unit_slope j * input + unit_bias j) 0)
      (unit_gain j) ?_
    by_cases slope_is_zero : unit_slope j = 0
    · exact ⟨0, max (unit_bias j) 0, fun input _ => by simp [slope_is_zero]⟩
    · exact affineOn_reluUnit (left_lt_middle.trans middle_lt_right)
        (no_kink_inside j j_in_units slope_is_zero)
  exact network_is_line.not_zigzag left_lt_middle middle_lt_right
    left_below_middle right_below_middle

/-- **One unit per turn.** If the network goes up and comes back down
`turn_count` times along an increasing run of inputs, it has at least
`turn_count` units. -/
theorem card_ge_of_zigzag
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    {checkpoints : ℕ → ℝ}
    (checkpoints_increase : StrictMono checkpoints)
    {turn_count : ℕ}
    (zigzags_at_checkpoints : ∀ i < turn_count,
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          (checkpoints (2 * i))
        < EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          (checkpoints (2 * i + 1))
      ∧ EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          (checkpoints (2 * i + 2))
        < EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          (checkpoints (2 * i + 1))) :
    let unit_count := units.card
    turn_count ≤ unit_count := by
  unfold_named_pieces
  -- Each turn holds a kink, so there is a unit for it.
  have every_turn_has_kink : ∀ i ∈ Finset.range turn_count,
      ∃ j ∈ units, unit_slope j ≠ 0 ∧
        ∃ crossing, checkpoints (2 * i) < crossing
          ∧ crossing < checkpoints (2 * i + 2)
          ∧ unit_slope j * crossing + unit_bias j = 0 := by
    intro i i_in_range
    obtain ⟨goes_up, comes_down⟩ :=
      zigzags_at_checkpoints i (Finset.mem_range.mp i_in_range)
    exact exists_kink_of_zigzag units unit_gain unit_slope unit_bias
      (checkpoints_increase (by omega)) (checkpoints_increase (by omega))
      goes_up comes_down
  rcases Nat.eq_zero_or_pos turn_count with rfl | turn_count_pos
  · exact Nat.zero_le _
  obtain ⟨first_unit, -⟩ :=
    every_turn_has_kink 0 (Finset.mem_range.mpr turn_count_pos)
  have : Nonempty Index := ⟨first_unit⟩
  choose! kink_unit kink_unit_spec using every_turn_has_kink
  -- Two different turns cannot share a unit: the stretches do not overlap and
  -- a unit has only one kink.
  have kink_unit_injective :
      Set.InjOn kink_unit (Finset.range turn_count : Set ℕ) := by
    intro turn turn_in_range other_turn other_turn_in_range same_unit
    obtain ⟨-, unit_slope_ne_zero, crossing, after_left, before_right,
        crossing_is_kink⟩ :=
      kink_unit_spec turn (Finset.mem_coe.mp turn_in_range)
    obtain ⟨-, -, other_crossing, other_after_left, other_before_right,
        other_crossing_is_kink⟩ :=
      kink_unit_spec other_turn (Finset.mem_coe.mp other_turn_in_range)
    rw [← same_unit] at other_crossing_is_kink
    have same_crossing : crossing = other_crossing :=
      mul_left_cancel₀ unit_slope_ne_zero (by linarith)
    by_contra turns_differ
    rcases Nat.lt_or_gt_of_ne turns_differ with turn_first | other_turn_first
    · have stretches_ordered :=
        checkpoints_increase.monotone
          (show 2 * turn + 2 ≤ 2 * other_turn by omega)
      linarith
    · have stretches_ordered :=
        checkpoints_increase.monotone
          (show 2 * other_turn + 2 ≤ 2 * turn by omega)
      linarith
  calc turn_count = (Finset.range turn_count).card :=
        (Finset.card_range turn_count).symm
    _ ≤ units.card :=
        Finset.card_le_card_of_injOn kink_unit
          (fun turn turn_in_range => (kink_unit_spec turn turn_in_range).1)
          kink_unit_injective

/-- **Depth separation.** `layer_count + 1` tent layers use
`2 (layer_count + 1)` neurons. A network with one hidden layer that stays
within one half of them at the `2 ^ (layer_count + 1) + 1` grid points has at
least `2 ^ layer_count` units. -/
theorem depth_separation
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    (layer_count : ℕ)
    (follows_zigzag : ∀ grid_index : ℕ, grid_index ≤ 2 ^ (layer_count + 1) →
      |EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          ((grid_index : ℝ) / 2 ^ (layer_count + 1))
        - APPLY_TENT^[layer_count + 1]
          ((grid_index : ℝ) / 2 ^ (layer_count + 1))|
        < 1 / 2) :
    let units_needed := 2 ^ layer_count  -- one unit per turn; the zigzag has 2 ^ layer_count turns
    let unit_count := units.card
    units_needed ≤ unit_count := by
  unfold_named_pieces
  -- At even grid points the tent is 0, so the network is below one half ...
  have low_at_even : ∀ grid_index : ℕ, grid_index ≤ 2 ^ (layer_count + 1) →
      Even grid_index →
      EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
        ((grid_index : ℝ) / 2 ^ (layer_count + 1)) < 1 / 2 := by
    intro grid_index index_on_grid index_even
    have closeness := follows_zigzag grid_index index_on_grid
    rw [iterate_tent_dyadic (layer_count + 1) grid_index index_on_grid,
      ite_eq_left index_even, sub_zero] at closeness
    exact (abs_lt.mp closeness).2
  -- ... and at odd grid points the tent is 1, so it is above one half.
  have high_at_odd : ∀ grid_index : ℕ, grid_index ≤ 2 ^ (layer_count + 1) →
      ¬ Even grid_index →
      1 / 2 < EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
        ((grid_index : ℝ) / 2 ^ (layer_count + 1)) := by
    intro grid_index index_on_grid index_odd
    have closeness := follows_zigzag grid_index index_on_grid
    rw [iterate_tent_dyadic (layer_count + 1) grid_index index_on_grid,
      ite_eq_right index_odd] at closeness
    have lower_side := (abs_lt.mp closeness).1
    linarith
  have two_pow_succ : 2 ^ (layer_count + 1) = 2 * 2 ^ layer_count := by
    rw [pow_succ, mul_comm]
  -- The grid points zigzag, so the network goes up and down once per pair.
  refine card_ge_of_zigzag units unit_gain unit_slope unit_bias
    (checkpoints := fun step : ℕ => (step : ℝ) / 2 ^ (layer_count + 1)) ?_ ?_
  · intro step other_step step_lt_other_step
    show (step : ℝ) / 2 ^ (layer_count + 1)
      < (other_step : ℝ) / 2 ^ (layer_count + 1)
    gcongr
  · intro i i_lt_turn_count
    have low_at_start := low_at_even (2 * i) (by omega) (even_two_mul i)
    have high_at_middle := high_at_odd (2 * i + 1) (by omega)
      (by rw [Nat.not_even_iff_odd]; exact odd_two_mul_add_one i)
    have low_at_end := low_at_even (2 * i + 2) (by omega) ⟨i + 1, by ring⟩
    exact ⟨low_at_start.trans high_at_middle, low_at_end.trans high_at_middle⟩

end Shallow

end SquigglyLine
