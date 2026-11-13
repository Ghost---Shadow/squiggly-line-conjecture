/-
Universal approximation, and what it costs.

Cut the interval `[0, 1]` into `piece_count` pieces. An `EVALUATE_RAMP` is
flat, then rises across one piece, then is flat again: two ReLU units.
`INTERPOLATE_WITH_RELU model piece_count ramp_count` is the network made of
the first `ramp_count` ramps, each scaled to follow `model` across its piece.
It has one hidden layer of `2 * ramp_count` units.

Definitions:

* `EVALUATE_RAMP`           one ramp, flat then rising then flat;
* `INTERPOLATE_WITH_RELU`   the network made of the first ramps.

Theorems:

* `ramp_of_le`, `ramp_of_mem`, `ramp_of_ge` : the three stretches of a ramp.
* `slope_nonneg` : a slope bound is never negative.
* `reluInterp_succ` : adding one more ramp.
* `reluInterp_spec` : after `ramp_count` ramps the network is within
  `2 * slope_limit / piece_count` of `model` on the first `ramp_count` pieces,
  and sits exactly on `model (ramp_count / piece_count)` beyond them.
* `relu_network_close` : so `2 * piece_count` units are within
  `2 * slope_limit / piece_count` of `model` on the whole interval.
* `universal_approximation` : for any `tolerance > 0` there is such a network
  within `tolerance` of `model`.
-/
import SquigglyLine.Supporting.NetworkShape.DepthSeparation

namespace SquigglyLine

/-! ### One ramp: two ReLU units -/

section Ramp

/-- A ramp across the piece number `piece_index` of `piece_count` pieces: flat
at zero, rising with slope one, then flat at `1 / piece_count`. It is the
difference of two ReLU units.
Python: `max(input - k / n, 0) - max(input - (k + 1) / n, 0)`. -/
noncomputable def EVALUATE_RAMP
    (piece_count : ℕ)
    (piece_index : ℕ)
    (input : ℝ) : ℝ :=
  let rises_at_start := max (input - piece_index / piece_count) 0
  let rises_at_end   := max (input - (piece_index + 1) / piece_count) 0
  rises_at_start - rises_at_end  -- the second unit cancels the slope after the piece

variable {piece_count piece_index : ℕ} {input : ℝ}

/-- Before its piece, a ramp is zero. -/
theorem ramp_of_le
    (piece_count_pos : (0 : ℝ) < piece_count)
    (input_before_piece : input ≤ piece_index / piece_count) :
    let ramp_value := EVALUATE_RAMP piece_count piece_index input
    ramp_value = 0 := by
  unfold_named_pieces
  have piece_width_pos : 0 < 1 / (piece_count : ℝ) :=
    one_div_pos.mpr piece_count_pos
  rw [EVALUATE_RAMP, add_div, max_eq_right (by linarith),
    max_eq_right (by linarith), sub_self]

/-- Inside its piece, a ramp rises with slope one. -/
theorem ramp_of_mem
    (input_after_start : (piece_index : ℝ) / piece_count ≤ input)
    (input_before_end : input ≤ (piece_index + 1) / piece_count) :
    let ramp_value := EVALUATE_RAMP piece_count piece_index input
    let rising_line := input - piece_index / piece_count  -- slope one, starting at zero
    ramp_value = rising_line := by
  unfold_named_pieces
  rw [EVALUATE_RAMP, max_eq_left (by linarith), max_eq_right (by linarith),
    sub_zero]

/-- After its piece, a ramp stays at its full height. -/
theorem ramp_of_ge
    (piece_count_pos : (0 : ℝ) < piece_count)
    (input_after_piece : ((piece_index : ℝ) + 1) / piece_count ≤ input) :
    let ramp_value  := EVALUATE_RAMP piece_count piece_index input
    let full_height : ℝ := 1 / piece_count  -- one piece wide, at slope one
    ramp_value = full_height := by
  unfold_named_pieces
  have piece_width_pos : 0 < 1 / (piece_count : ℝ) :=
    one_div_pos.mpr piece_count_pos
  rw [add_div] at input_after_piece
  rw [EVALUATE_RAMP, add_div, max_eq_left (by linarith),
    max_eq_left (by linarith)]
  ring

end Ramp

/-! ### The network that follows `model` -/

section Network

/-- The network made of the first `ramp_count` ramps, each scaled to follow
`model` across its piece.
Python: `model(0) + sum(piece_count * (model((i + 1) / piece_count)
- model(i / piece_count)) * ramp(i, input) for i in range(ramp_count))`. -/
noncomputable def INTERPOLATE_WITH_RELU
    (model : RealFunction)
    (piece_count : ℕ)
    (ramp_count : ℕ)
    (input : ℝ) : ℝ :=
  model 0 + ∑ i ∈ Finset.range ramp_count,
    piece_count * (model (((i : ℝ) + 1) / piece_count)
      - model ((i : ℝ) / piece_count)) * EVALUATE_RAMP piece_count i input

variable {model : RealFunction} {slope_limit : ℝ} {piece_count : ℕ}

/-- A slope bound is never negative. -/
theorem slope_nonneg
    (slope_is_bounded :
      ∀ input other_input,
        |model input - model other_input|
          ≤ slope_limit * |input - other_input|) :
    0 ≤ slope_limit := by
  have unit_step_bound := slope_is_bounded 0 1
  rw [zero_sub, abs_neg, abs_one, mul_one] at unit_step_bound
  exact (abs_nonneg _).trans unit_step_bound

/-- Adding one more ramp. -/
theorem reluInterp_succ
    (model : RealFunction)
    (piece_count : ℕ)
    (ramp_count : ℕ)
    (input : ℝ) :
    let with_one_more :=
      INTERPOLATE_WITH_RELU model piece_count (ramp_count + 1) input
    let before :=
      INTERPOLATE_WITH_RELU model piece_count ramp_count input
    let new_ramp : ℝ  :=
      piece_count * (model (((ramp_count : ℝ) + 1) / piece_count)
        - model ((ramp_count : ℝ) / piece_count))
      * EVALUATE_RAMP piece_count ramp_count input  -- the ramp scaled to rise by the change of `model`
    with_one_more = before + new_ramp := by
  unfold_named_pieces
  rw [INTERPOLATE_WITH_RELU, Finset.sum_range_succ, INTERPOLATE_WITH_RELU,
    add_assoc]

/-- **Piece by piece.** After `ramp_count` ramps the network is within
`2 * slope_limit / piece_count` of `model` on the first `ramp_count` pieces,
and sits exactly on `model (ramp_count / piece_count)` beyond them. -/
theorem reluInterp_spec
    (slope_is_bounded :
      ∀ input other_input,
        |model input - model other_input|
          ≤ slope_limit * |input - other_input|)
    (piece_count_pos : (0 : ℝ) < piece_count)
    (ramp_count : ℕ) :
    let network_value := INTERPOLATE_WITH_RELU model piece_count ramp_count
    let covered_is_close := ∀ input : ℝ, 0 ≤ input →
      input ≤ ramp_count / piece_count →
      |network_value input - model input|
        ≤ 2 * slope_limit / piece_count  -- two errors of `slope_limit * piece width`
    let rest_is_flat := ∀ input : ℝ, (ramp_count : ℝ) / piece_count ≤ input →
      network_value input = model (ramp_count / piece_count)
    covered_is_close ∧ rest_is_flat := by
  unfold_named_pieces
  have slope_limit_nonneg := slope_nonneg slope_is_bounded
  have piece_width_pos : 0 < 1 / (piece_count : ℝ) :=
    one_div_pos.mpr piece_count_pos
  induction ramp_count with
  | zero =>
    constructor
    · -- No ramps yet: the only covered input is 0, where the network is exact.
      intro input input_nonneg input_le_start
      have input_is_zero : input = 0 :=
        le_antisymm (by simpa using input_le_start) input_nonneg
      subst input_is_zero
      rw [show INTERPOLATE_WITH_RELU model piece_count 0 0 - model 0 = 0 by
            simp [INTERPOLATE_WITH_RELU],
        abs_zero]
      exact div_nonneg (by linarith) piece_count_pos.le
    · intro input _
      simp [INTERPOLATE_WITH_RELU]
  | succ ramp_count spec_for_fewer_ramps =>
    obtain ⟨close_on_covered, flat_beyond⟩ := spec_for_fewer_ramps
    constructor
    · intro input input_nonneg input_le_end
      rw [Nat.cast_succ] at input_le_end
      rcases le_total input (ramp_count / piece_count) with
        input_in_covered | input_in_new_piece
      · -- The new ramp is still flat here, so nothing changes.
        rw [reluInterp_succ, ramp_of_le piece_count_pos input_in_covered,
          mul_zero, add_zero]
        exact close_on_covered input input_nonneg input_in_covered
      · -- Inside the new piece the old network is flat, and the new ramp
        -- adds at most one piece width of change, twice over.
        have offset_nonneg : 0 ≤ input - ramp_count / piece_count := by
          linarith
        have offset_le_width :
            input - ramp_count / piece_count ≤ 1 / piece_count := by
          rw [add_div] at input_le_end
          linarith
        have old_value_error :
            |model (ramp_count / piece_count) - model input|
              ≤ slope_limit * (1 / piece_count) :=
          calc |model (ramp_count / piece_count) - model input|
              ≤ slope_limit * |(ramp_count : ℝ) / piece_count - input| :=
                slope_is_bounded _ _
            _ = slope_limit * (input - ramp_count / piece_count) := by
                rw [abs_sub_comm, abs_of_nonneg offset_nonneg]
            _ ≤ slope_limit * (1 / piece_count) :=
                mul_le_mul_of_nonneg_left offset_le_width slope_limit_nonneg
        have step_size :
            |model (((ramp_count : ℝ) + 1) / piece_count)
              - model (ramp_count / piece_count)|
              ≤ slope_limit * (1 / piece_count) :=
          calc |model (((ramp_count : ℝ) + 1) / piece_count)
                - model (ramp_count / piece_count)|
              ≤ slope_limit
                * |((ramp_count : ℝ) + 1) / piece_count
                  - ramp_count / piece_count| :=
                slope_is_bounded _ _
            _ = slope_limit * (1 / piece_count) := by
                rw [add_div, add_sub_cancel_left,
                  abs_of_pos piece_width_pos]
        have ramp_term_size :
            |piece_count * (model (((ramp_count : ℝ) + 1) / piece_count)
                - model (ramp_count / piece_count))
              * (input - ramp_count / piece_count)|
              ≤ slope_limit * (1 / piece_count) := by
          rw [abs_mul, abs_mul, abs_of_pos piece_count_pos,
            abs_of_nonneg offset_nonneg]
          calc piece_count * |model (((ramp_count : ℝ) + 1) / piece_count)
                  - model (ramp_count / piece_count)|
                * (input - ramp_count / piece_count)
              ≤ piece_count * (slope_limit * (1 / piece_count))
                  * (1 / piece_count) :=
                mul_le_mul (mul_le_mul_of_nonneg_left step_size
                    piece_count_pos.le)
                  offset_le_width offset_nonneg
                  (mul_nonneg piece_count_pos.le
                    (mul_nonneg slope_limit_nonneg piece_width_pos.le))
            _ = slope_limit * (1 / piece_count) := by
                field_simp
        rw [reluInterp_succ, flat_beyond input input_in_new_piece,
          ramp_of_mem input_in_new_piece input_le_end]
        calc |model (ramp_count / piece_count)
                + piece_count * (model (((ramp_count : ℝ) + 1) / piece_count)
                  - model (ramp_count / piece_count))
                  * (input - ramp_count / piece_count)
                - model input|
            = |(model (ramp_count / piece_count) - model input)
                + piece_count * (model (((ramp_count : ℝ) + 1) / piece_count)
                  - model (ramp_count / piece_count))
                  * (input - ramp_count / piece_count)| := by
              congr 1
              ring
          _ ≤ |model (ramp_count / piece_count) - model input|
                + |piece_count
                  * (model (((ramp_count : ℝ) + 1) / piece_count)
                    - model (ramp_count / piece_count))
                  * (input - ramp_count / piece_count)| :=
              abs_add_le _ _
          _ ≤ slope_limit * (1 / piece_count)
                + slope_limit * (1 / piece_count) :=
              add_le_add old_value_error ramp_term_size
          _ = 2 * slope_limit / piece_count := by ring
    · -- Beyond the new piece the new ramp is at full height, which lands the
      -- network exactly on the next grid value.
      intro input input_after_new_piece
      rw [Nat.cast_succ] at input_after_new_piece ⊢
      have input_after_covered : (ramp_count : ℝ) / piece_count ≤ input := by
        rw [add_div] at input_after_new_piece
        linarith
      rw [reluInterp_succ, flat_beyond input input_after_covered,
        ramp_of_ge piece_count_pos input_after_new_piece]
      field_simp
      ring

/-- **A network of `2 * piece_count` units is within
`2 * slope_limit / piece_count` of `model`.** -/
theorem relu_network_close
    (slope_is_bounded :
      ∀ input other_input,
        |model input - model other_input|
          ≤ slope_limit * |input - other_input|)
    (piece_count_pos : (0 : ℝ) < piece_count)
    {input : ℝ}
    (input_nonneg : 0 ≤ input)
    (input_le_one : input ≤ 1) :
    let approximation_error :=
      |INTERPOLATE_WITH_RELU model piece_count piece_count input - model input|
    let error_bound := 2 * slope_limit / piece_count  -- from `reluInterp_spec`
    approximation_error ≤ error_bound := by
  unfold_named_pieces
  exact (reluInterp_spec slope_is_bounded piece_count_pos piece_count).1
    input input_nonneg (by rwa [div_self piece_count_pos.ne'])

/-- **Universal approximation.** A function on `[0, 1]` with slope at most
`slope_limit` is within any `tolerance > 0` of a ReLU network with one hidden
layer. -/
theorem universal_approximation
    (slope_is_bounded :
      ∀ input other_input,
        |model input - model other_input|
          ≤ slope_limit * |input - other_input|)
    {tolerance : ℝ}
    (tolerance_pos : 0 < tolerance) :
    let unit_interval := Set.Icc (0 : ℝ) 1
    let is_within_tolerance := fun (pieces_used : ℕ) (input : ℝ) =>
      |INTERPOLATE_WITH_RELU model pieces_used pieces_used input - model input|
        ≤ tolerance
    ∃ needed_piece_count : ℕ, ∀ input ∈ unit_interval,
      is_within_tolerance needed_piece_count input := by
  unfold_named_pieces
  beta_reduce
  have slope_limit_nonneg := slope_nonneg slope_is_bounded
  -- Enough pieces that `2 * slope_limit / piece_count` drops below the
  -- tolerance.
  obtain ⟨chosen_piece_count, chosen_count_large⟩ :=
    exists_nat_gt (2 * slope_limit / tolerance)
  have chosen_count_pos : (0 : ℝ) < chosen_piece_count :=
    lt_of_le_of_lt (div_nonneg (by linarith) tolerance_pos.le)
      chosen_count_large
  refine ⟨chosen_piece_count, fun input input_in_unit => ?_⟩
  calc |INTERPOLATE_WITH_RELU model chosen_piece_count chosen_piece_count input
        - model input|
      ≤ 2 * slope_limit / chosen_piece_count :=
        relu_network_close slope_is_bounded chosen_count_pos
          input_in_unit.1 input_in_unit.2
    _ ≤ tolerance := by
        rw [div_lt_iff₀ tolerance_pos] at chosen_count_large
        rw [div_le_iff₀ chosen_count_pos]
        linarith

end Network

end SquigglyLine
