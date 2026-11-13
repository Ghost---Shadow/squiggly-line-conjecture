/-
A network for which the conjecture is true.

Stack `layer_count` of the two-neuron folds of `Depth.lean`. The curve this
network draws passes within `1 / 2 ^ layer_count` of every point of the unit
square. Each layer halves the distance.

So for this family "more layers, squigglier, closer" holds, with an
exponential rate. The weights are chosen, not random.

Theorems:

* `iterate_tent_covers`         every label in the unit interval is taken at
                                an input within `1 / 2 ^ layer_count`;
* `nearestDist_iterate_tent_le` so the curve is within that distance of every
                                point of the unit square.
-/
import SquigglyLine.Networks.Bridge
import SquigglyLine.Theorem.Oscillation

namespace SquigglyLine

/-- **Each fold halves the distance.** For any input and any label in the unit
interval, the `layer_count`-fold network takes that label at some input within
`1 / 2 ^ layer_count`. -/
theorem iterate_tent_covers
    (layer_count : ℕ)
    {input label : ℝ}
    (input_in_unit : input ∈ Set.Icc (0 : ℝ) 1)
    (label_in_unit : label ∈ Set.Icc (0 : ℝ) 1) :
    let unit_interval := Set.Icc (0 : ℝ) 1
    let max_gap := 1 / 2 ^ layer_count  -- each layer halves the gap, starting from 1
    let is_close := fun (other_input : ℝ) => |input - other_input| ≤ max_gap
    let hits_label := fun (other_input : ℝ) =>
      APPLY_TENT^[layer_count] other_input = label
    ∃ other_input ∈ unit_interval,
      is_close other_input ∧ hits_label other_input := by
  unfold_named_pieces
  beta_reduce
  induction layer_count generalizing input with
  | zero =>
    -- No layers: the network is the identity, so the label itself is the answer.
    refine ⟨label, label_in_unit, ?_, rfl⟩
    rw [pow_zero, div_one, abs_le]
    constructor <;>
      linarith [input_in_unit.1, input_in_unit.2,
        label_in_unit.1, label_in_unit.2]
  | succ layer_count covered_by_fewer_layers =>
    -- Fold the input once, use the shorter network on the folded input, and
    -- unfold the answer it finds.
    obtain ⟨folded_answer, answer_in_unit, answer_is_close,
        answer_hits_label⟩ :=
      covered_by_fewer_layers (tent_mem_Icc input_in_unit.1 input_in_unit.2)
    have gap_halves :
        (1 : ℝ) / 2 ^ (layer_count + 1) = 1 / 2 ^ layer_count / 2 := by
      rw [pow_succ]
      field_simp
    rcases le_total input (1 / 2) with input_in_left_half | input_in_right_half
    · -- Left half: the tent doubles the input, so halve the answer.
      refine ⟨folded_answer / 2,
        ⟨by linarith [answer_in_unit.1], by linarith [answer_in_unit.2]⟩,
        ?_, ?_⟩
      · rw [tent_of_le_half input_in_unit.1 input_in_left_half]
          at answer_is_close
        rw [gap_halves,
          show input - folded_answer / 2 = (2 * input - folded_answer) / 2
            by ring,
          abs_div, abs_two]
        exact div_le_div_of_nonneg_right answer_is_close (by norm_num)
      · rw [Function.iterate_succ_apply,
          tent_of_le_half (by linarith [answer_in_unit.1])
            (by linarith [answer_in_unit.2]),
          show 2 * (folded_answer / 2) = folded_answer by ring,
          answer_hits_label]
    · -- Right half: the tent mirrors the input, so mirror the answer.
      refine ⟨1 - folded_answer / 2,
        ⟨by linarith [answer_in_unit.2], by linarith [answer_in_unit.1]⟩,
        ?_, ?_⟩
      · rw [tent_of_half_le input_in_right_half] at answer_is_close
        rw [gap_halves,
          show input - (1 - folded_answer / 2)
            = -((2 - 2 * input - folded_answer) / 2) by ring,
          abs_neg, abs_div, abs_two]
        exact div_le_div_of_nonneg_right answer_is_close (by norm_num)
      · rw [Function.iterate_succ_apply,
          tent_of_half_le (by linarith [answer_in_unit.2]),
          show 2 - 2 * (1 - folded_answer / 2) = folded_answer by ring,
          answer_hits_label]

/-- **More layers, closer.** The curve drawn by `layer_count` two-neuron layers
passes within `1 / 2 ^ layer_count` of every point of the unit square. -/
theorem nearestDist_iterate_tent_le
    (layer_count : ℕ)
    (data_point : DataPoint ℝ)
    (input_in_unit : data_point.1 ∈ Set.Icc (0 : ℝ) 1)
    (label_in_unit : data_point.2 ∈ Set.Icc (0 : ℝ) 1) :
    let nearest_distance :=
      GET_NEAREST_DISTANCE (APPLY_TENT^[layer_count]) data_point
    let max_gap := 1 / 2 ^ layer_count  -- the gap found by `iterate_tent_covers`
    nearest_distance ≤ max_gap := by
  unfold_named_pieces
  obtain ⟨other_input, -, other_input_is_close, other_input_hits_label⟩ :=
    iterate_tent_covers layer_count input_in_unit label_in_unit
  -- The curve point above `other_input` is a candidate for the nearest point.
  calc GET_NEAREST_DISTANCE (APPLY_TENT^[layer_count]) data_point
      ≤ dist (EMBED_DATA_POINT data_point)
          (EMBED_DATA_POINT
            (other_input, APPLY_TENT^[layer_count] other_input)) :=
        Metric.infDist_le_dist_of_mem
          (footpoint_mem_curve _
            (other_input, APPLY_TENT^[layer_count] other_input))
    _ = |data_point.1 - other_input| := by
        simp [dist_embed, other_input_hits_label, Real.dist_eq,
          Real.sqrt_sq_eq_abs]
    _ ≤ 1 / 2 ^ layer_count := other_input_is_close

end SquigglyLine
