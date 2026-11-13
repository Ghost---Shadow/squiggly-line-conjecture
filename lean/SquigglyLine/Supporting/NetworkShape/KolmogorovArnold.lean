/-
Kolmogorov–Arnold networks: a learnable curve on an edge is a few folds.

A node of a Kolmogorov–Arnold network adds up one learnable curve per input:
`node(inputs) = Σ curve i (inputs i)`. `UniversalApproximation.lean` says a
curve of slope at most `slope_limit` on `[0, 1]` is within
`2 * slope_limit / piece_count` of a ReLU network with `piece_count` pieces.
Do that on every edge and the node is within
`2 * (Σ slope_limit i) / piece_count` of a plain ReLU layer. So the number of
folds a node needs goes as the total slope of its curves over the error
allowed.

Theorems:

* `abs_kanNode_sub_le` : with `piece_count` pieces per edge, the ReLU version
  of a node is within `2 * (Σ slope_limit i) / piece_count` of the node;
* `exists_pieces_kanNode_close` : for any tolerance there is a number of
  pieces that brings the ReLU version within it.
-/
import SquigglyLine.Supporting.NetworkShape.UniversalApproximation

namespace SquigglyLine

variable {Inputs : Type*} [Fintype Inputs]

/-- **An edge curve is a few folds.** Replace every edge curve of a node by its
ReLU network with `piece_count` pieces. On the unit cube the node changes by at
most `2 * (Σ slope_limit i) / piece_count`. -/
theorem abs_kanNode_sub_le
    {curve : Inputs → RealFunction}
    {slope_limit : Inputs → ℝ}
    (slopes_are_bounded :
      ∀ i input other_input,
        |curve i input - curve i other_input|
          ≤ slope_limit i * |input - other_input|)
    {piece_count : ℕ}
    (piece_count_pos : (0 : ℝ) < piece_count)
    {inputs : Inputs → ℝ}
    (inputs_nonneg : ∀ i, 0 ≤ inputs i)
    (inputs_le_one : ∀ i, inputs i ≤ 1) :
    let relu_node   :=
      ∑ i, INTERPOLATE_WITH_RELU (curve i) piece_count piece_count (inputs i)
    let kan_node    := ∑ i, curve i (inputs i)
    let node_error  := |relu_node - kan_node|
    let error_bound := 2 * (∑ i, slope_limit i) / piece_count  -- `2 * slope_limit i / piece_count` per edge, from `relu_network_close`
    node_error ≤ error_bound := by
  unfold_named_pieces
  rw [← Finset.sum_sub_distrib]
  calc |∑ i, (INTERPOLATE_WITH_RELU (curve i) piece_count piece_count
            (inputs i) - curve i (inputs i))|
      ≤ ∑ i, |INTERPOLATE_WITH_RELU (curve i) piece_count piece_count
          (inputs i) - curve i (inputs i)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, 2 * slope_limit i / piece_count :=
        Finset.sum_le_sum fun i _ =>
          relu_network_close (slopes_are_bounded i) piece_count_pos
            (inputs_nonneg i) (inputs_le_one i)
    _ = 2 * (∑ i, slope_limit i) / piece_count := by
        simp only [Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]

/-- **Folds needed go as total slope over error.** For any tolerance there is a
number of pieces, the same on every edge, that brings the ReLU version of the
node within the tolerance everywhere on the unit cube. -/
theorem exists_pieces_kanNode_close
    {curve : Inputs → RealFunction}
    {slope_limit : Inputs → ℝ}
    (slopes_are_bounded :
      ∀ i input other_input,
        |curve i input - curve i other_input|
          ≤ slope_limit i * |input - other_input|)
    {tolerance : ℝ}
    (tolerance_pos : 0 < tolerance) :
    let are_nonneg := fun (inputs : Inputs → ℝ) => ∀ i, 0 ≤ inputs i
    let are_le_one := fun (inputs : Inputs → ℝ) => ∀ i, inputs i ≤ 1
    let is_within_tolerance :=
      fun (piece_count : ℕ) (inputs : Inputs → ℝ) =>
      |∑ i, INTERPOLATE_WITH_RELU (curve i) piece_count piece_count (inputs i)
          - ∑ i, curve i (inputs i)|
        ≤ tolerance
    ∃ needed_piece_count : ℕ, ∀ inputs : Inputs → ℝ,
      are_nonneg inputs → are_le_one inputs →
        is_within_tolerance needed_piece_count inputs := by
  unfold_named_pieces
  beta_reduce
  have total_slope_nonneg : 0 ≤ ∑ i, slope_limit i :=
    Finset.sum_nonneg fun i _ => slope_nonneg (slopes_are_bounded i)
  -- Enough pieces: one more than `2 * (Σ slope_limit i) / tolerance`.
  obtain ⟨chosen_piece_count, chosen_piece_count_def⟩ :
      ∃ chosen : ℕ,
        chosen = ⌈2 * (∑ i, slope_limit i) / tolerance⌉₊ + 1 :=
    ⟨_, rfl⟩
  refine ⟨chosen_piece_count, fun inputs inputs_nonneg inputs_le_one => ?_⟩
  have piece_count_pos : (0 : ℝ) < (chosen_piece_count : ℝ) := by
    rw [chosen_piece_count_def]
    positivity
  have node_bound :
      |∑ i, INTERPOLATE_WITH_RELU (curve i) chosen_piece_count
            chosen_piece_count (inputs i)
          - ∑ i, curve i (inputs i)|
        ≤ 2 * (∑ i, slope_limit i) / chosen_piece_count :=
    abs_kanNode_sub_le slopes_are_bounded piece_count_pos inputs_nonneg
      inputs_le_one
  refine node_bound.trans ?_
  rw [div_le_iff₀ piece_count_pos]
  have ceil_le_piece_count :
      2 * (∑ i, slope_limit i) / tolerance
        ≤ (chosen_piece_count : ℝ) := by
    rw [chosen_piece_count_def]
    push_cast
    exact (Nat.le_ceil _).trans (by linarith)
  calc 2 * (∑ i, slope_limit i)
      = 2 * (∑ i, slope_limit i) / tolerance * tolerance := by field_simp
    _ ≤ (chosen_piece_count : ℝ) * tolerance :=
        mul_le_mul_of_nonneg_right ceil_le_piece_count tolerance_pos.le
    _ = tolerance * (chosen_piece_count : ℝ) := mul_comm _ _

end SquigglyLine
