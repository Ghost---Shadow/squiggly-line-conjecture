/-
Mixing: five more things that are averages, and one that is not.

* **Graph networks.** A message-passing layer replaces each node by an average
  over nodes. If every weight is at least `weight_floor`, a layer shrinks the
  spread of the nodes by `1 - node_count * weight_floor`, and `layer_count`
  layers by that to the power `layer_count`.
* **The diffusion noising schedule.** Each step keeps the share
  `1 - noise_rate` of the signal and of the old noise and adds `noise_rate` of
  fresh noise. Signal plus noise stays one, and the signal's share is the
  product of the `1 - noise_rate`.
* **Data augmentation.** Averaging a model over a group of moves that keep
  distances gives a model that ignores those moves and is no steeper.
* **The baseline.** Subtracting a baseline from the reward does not change the
  average push on the scores of a softmax policy.
* **Classifier-free guidance is not an average.** Its weights are
  `1 + guidance_strength` and `-guidance_strength`. It moves
  `1 + guidance_strength` times as far as the plain step, and for a positive
  strength it leaves the stretch between the two predictions.

Definitions: `APPLY_MESSAGE_PASSING`, `TAKE_NOISING_STEP`,
`AVERAGE_OVER_MOVES`, `APPLY_GUIDANCE`.

Theorems:
* `abs_messagePassing_sub_le`          one layer shrinks the spread;
* `abs_iterate_messagePassing_sub_le`  depth shrinks it geometrically;
* `noisingStep_sum`                    a noising step keeps the variance at
                                       one;
* `iterate_noisingStep_signal`         the signal's share is a product;
* `averageOverMoves_smul`              the averaged model ignores the moves;
* `lipschitzWith_averageOverMoves`     and it is no steeper;
* `sum_mul_baseline_eq_zero`           a baseline pushes nothing on average;
* `sum_mul_sub_baseline`               so subtracting one changes no push;
* `guidance_sub`                       guidance moves `1 + strength` times as
                                       far;
* `norm_guidance_sub`                  the same, for lengths;
* `guidance_notMem_segment`            guidance is not an average.
-/
import Mathlib.Analysis.Convex.Segment
import SquigglyLine.Supporting.NetworkShape.AttentionRate
import SquigglyLine.Theorem.Sandwich

namespace SquigglyLine

open Real NNReal

/-- The share of signal and the share of noise in the variance of a noised
input. Python: `(signal_share, noise_share)`. -/
abbrev VarianceSplit := ℝ × ℝ

variable {Nodes : Type*} [Fintype Nodes]

/-- One layer of message passing: each node becomes a weighted sum of the
nodes, with the weights `node_weights node j` that `node` gives to node `j`.
Python: `[sum(node_weights[n][j] * node_values[j] for j in nodes)
for n in nodes]`. -/
def APPLY_MESSAGE_PASSING
    (node_weights : Nodes → Nodes → ℝ)
    (node_values : Nodes → ℝ) : Nodes → ℝ :=
  fun node => ∑ j, node_weights node j * node_values j

/-- **A message-passing layer shrinks the spread.** If every row of weights
adds to one and every weight is at least `weight_floor`, two nodes end no
further apart than `1 - node_count * weight_floor` times the range of the
values. -/
theorem abs_messagePassing_sub_le
    {node_weights : Nodes → Nodes → ℝ}
    {weight_floor lower_bound upper_bound : ℝ}
    (weights_above_floor : ∀ i j, weight_floor ≤ node_weights i j)
    (rows_sum_to_one : ∀ i, ∑ j, node_weights i j = 1)
    {node_values : Nodes → ℝ}
    (values_above_lower : ∀ j, lower_bound ≤ node_values j)
    (values_below_upper : ∀ j, node_values j ≤ upper_bound)
    (node other_node : Nodes) :
    let passed       := APPLY_MESSAGE_PASSING node_weights node_values node
    let other_passed :=
      APPLY_MESSAGE_PASSING node_weights node_values other_node
    let gap_size     := |passed - other_passed|
    let disagreeable := 1 - Fintype.card Nodes * weight_floor  -- `node_count * weight_floor` is shared, the rest can differ
    let value_range  := upper_bound - lower_bound
    gap_size ≤ disagreeable * value_range := by
  unfold_named_pieces
  have step :
      |∑ j, node_weights node j * node_values j
          - ∑ j, node_weights other_node j * node_values j|
        ≤ (1 - Fintype.card Nodes * weight_floor)
          * (upper_bound - lower_bound) :=
    abs_sum_mul_sub_sum_mul_le (weights_above_floor node)
      (weights_above_floor other_node) (rows_sum_to_one node)
      (rows_sum_to_one other_node) values_above_lower values_below_upper
  exact step

/-- **Depth blurs the nodes.** After `layer_count` layers any two nodes differ
by at most `(1 - node_count * weight_floor) ^ layer_count` times the range
they started in. -/
theorem abs_iterate_messagePassing_sub_le
    [Nonempty Nodes]
    {node_weights : Nodes → Nodes → ℝ}
    {weight_floor lower_bound upper_bound : ℝ}
    (shrink_nonneg : 0 ≤ 1 - Fintype.card Nodes * weight_floor)
    (weights_above_floor : ∀ i j, weight_floor ≤ node_weights i j)
    (rows_sum_to_one : ∀ i, ∑ j, node_weights i j = 1)
    {node_values : Nodes → ℝ}
    (values_above_lower : ∀ j, lower_bound ≤ node_values j)
    (values_below_upper : ∀ j, node_values j ≤ upper_bound)
    (layer_count : ℕ)
    (node other_node : Nodes) :
    let passed       :=
      (APPLY_MESSAGE_PASSING node_weights)^[layer_count] node_values node
    let other_passed :=
      (APPLY_MESSAGE_PASSING node_weights)^[layer_count] node_values
        other_node
    let gap_size     := |passed - other_passed|
    let shrink       := 1 - Fintype.card Nodes * weight_floor  -- one layer's factor
    let value_range  := upper_bound - lower_bound
    gap_size ≤ shrink ^ layer_count * value_range := by
  unfold_named_pieces
  -- After any depth, all values sit in a band at most that much narrower.
  have values_in_narrowing_band : ∀ depth : ℕ,
      ∃ new_lower new_upper : ℝ,
      (∀ j, new_lower ≤ (APPLY_MESSAGE_PASSING node_weights)^[depth]
        node_values j) ∧
      (∀ j, (APPLY_MESSAGE_PASSING node_weights)^[depth] node_values j
        ≤ new_upper) ∧
      new_upper - new_lower
        ≤ (1 - Fintype.card Nodes * weight_floor) ^ depth
          * (upper_bound - lower_bound) := by
    intro depth
    induction depth with
    | zero =>
      exact ⟨lower_bound, upper_bound, values_above_lower,
        values_below_upper, by simp⟩
    | succ depth previous_band =>
      obtain ⟨band_lower, band_upper, above_band_lower, below_band_upper,
        band_width⟩ := previous_band
      set previous := (APPLY_MESSAGE_PASSING node_weights)^[depth]
        node_values with previous_def
      obtain ⟨lowest_node, -, lowest_is_lowest⟩ :=
        Finset.exists_min_image Finset.univ
          (fun j => APPLY_MESSAGE_PASSING node_weights previous j)
          Finset.univ_nonempty
      obtain ⟨highest_node, -, highest_is_highest⟩ :=
        Finset.exists_max_image Finset.univ
          (fun j => APPLY_MESSAGE_PASSING node_weights previous j)
          Finset.univ_nonempty
      refine ⟨APPLY_MESSAGE_PASSING node_weights previous lowest_node,
        APPLY_MESSAGE_PASSING node_weights previous highest_node, ?_, ?_,
        ?_⟩
      · intro j
        rw [Function.iterate_succ_apply']
        exact lowest_is_lowest j (Finset.mem_univ j)
      · intro j
        rw [Function.iterate_succ_apply']
        exact highest_is_highest j (Finset.mem_univ j)
      · have gap_bound :
            |APPLY_MESSAGE_PASSING node_weights previous highest_node
              - APPLY_MESSAGE_PASSING node_weights previous lowest_node|
            ≤ (1 - Fintype.card Nodes * weight_floor)
              * (band_upper - band_lower) :=
          abs_messagePassing_sub_le weights_above_floor rows_sum_to_one
            above_band_lower below_band_upper highest_node lowest_node
        calc APPLY_MESSAGE_PASSING node_weights previous highest_node
              - APPLY_MESSAGE_PASSING node_weights previous lowest_node
            ≤ (1 - Fintype.card Nodes * weight_floor)
              * (band_upper - band_lower) := (le_abs_self _).trans gap_bound
          _ ≤ (1 - Fintype.card Nodes * weight_floor)
              * ((1 - Fintype.card Nodes * weight_floor) ^ depth
                * (upper_bound - lower_bound)) :=
              mul_le_mul_of_nonneg_left band_width shrink_nonneg
          _ = (1 - Fintype.card Nodes * weight_floor) ^ (depth + 1)
              * (upper_bound - lower_bound) := by ring
  obtain ⟨band_lower, band_upper, above_band_lower, below_band_upper,
    band_width⟩ := values_in_narrowing_band layer_count
  rw [abs_le]
  constructor <;> linarith [above_band_lower node, below_band_upper node,
    above_band_lower other_node, below_band_upper other_node]

/-- One noising step, on the pair (share of signal, share of noise) of the
variance: keep `1 - noise_rate` of each and add `noise_rate` of fresh noise.
Python: `((1 - rate) * signal, (1 - rate) * noise + rate)`. -/
def TAKE_NOISING_STEP
    (noise_rate : ℝ)
    (split : VarianceSplit) : VarianceSplit :=
  ((1 - noise_rate) * split.1, (1 - noise_rate) * split.2 + noise_rate)

/-- **The schedule keeps the total variance at one.** -/
theorem noisingStep_sum
    (noise_rate : ℝ)
    {split : VarianceSplit}
    (split_sums_to_one : split.1 + split.2 = 1) :
    let stepped       := TAKE_NOISING_STEP noise_rate split
    let stepped_total := stepped.1 + stepped.2
    let full_variance : ℝ := 1
    stepped_total = full_variance := by
  unfold_named_pieces
  simp only [TAKE_NOISING_STEP]
  linear_combination (1 - noise_rate) * split_sums_to_one

/-- **The signal's share is the product of the factors `1 - noise_rate`.**
With the same `noise_rate` at every step it is `(1 - noise_rate) ^ step_count`
of what it was. -/
theorem iterate_noisingStep_signal
    (noise_rate : ℝ)
    (split : VarianceSplit)
    (step_count : ℕ) :
    let signal_after    :=
      ((TAKE_NOISING_STEP noise_rate)^[step_count] split).1
    let signal_expected := (1 - noise_rate) ^ step_count * split.1  -- one factor of 1 - noise_rate per step
    signal_after = signal_expected := by
  unfold_named_pieces
  induction step_count with
  | zero => simp
  | succ step_count previous_steps =>
    rw [Function.iterate_succ_apply']
    simp only [TAKE_NOISING_STEP]
    rw [previous_steps]
    ring

variable {Moves Inputs : Type*} [Group Moves] [Fintype Moves]
  [MulAction Moves Inputs]

/-- A model averaged over a group of moves of the input.
Python: `mean(model(move(input)) for move in moves)`. -/
noncomputable def AVERAGE_OVER_MOVES
    (Moves : Type*) [Group Moves] [Fintype Moves] [MulAction Moves Inputs]
    (model : Model Inputs)
    (input : Inputs) : ℝ :=
  (Fintype.card Moves : ℝ)⁻¹ * ∑ move : Moves, model (move • input)

/-- **The averaged model ignores the moves.** -/
theorem averageOverMoves_smul
    (model : Model Inputs)
    (move : Moves)
    (input : Inputs) :
    let averaged_after_move := AVERAGE_OVER_MOVES Moves model (move • input)
    let averaged            := AVERAGE_OVER_MOVES Moves model input
    averaged_after_move = averaged := by
  unfold_named_pieces
  simp only [AVERAGE_OVER_MOVES, smul_smul]
  congr 1
  -- Composing with one more move just reorders the moves in the sum.
  exact Fintype.sum_equiv (Equiv.mulRight move) _ _ fun other_move => rfl

/-- **And it is no steeper**, when the moves keep distances. -/
theorem lipschitzWith_averageOverMoves
    [PseudoMetricSpace Inputs]
    {model : Model Inputs}
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit model)
    (moves_keep_distances :
      ∀ (move : Moves) (input other_input : Inputs),
        dist (move • input) (move • other_input) ≤ dist input other_input) :
    let averaged_model : Model Inputs := AVERAGE_OVER_MOVES Moves model
    LipschitzWith slope_limit averaged_model := by
  unfold_named_pieces
  have count_pos : (0 : ℝ) < Fintype.card Moves := by
    exact_mod_cast Fintype.card_pos
  refine LipschitzWith.of_dist_le_mul fun input other_input => ?_
  have move_error_bound : ∀ move : Moves,
      |model (move • input) - model (move • other_input)|
        ≤ slope_limit * dist input other_input := fun move => by
    have slope_step :=
      slope_is_bounded.dist_le_mul (move • input) (move • other_input)
    rw [Real.dist_eq] at slope_step
    exact slope_step.trans (mul_le_mul_of_nonneg_left
      (moves_keep_distances move input other_input) slope_limit.coe_nonneg)
  rw [Real.dist_eq, AVERAGE_OVER_MOVES, AVERAGE_OVER_MOVES, ← mul_sub,
    ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (inv_pos.mpr count_pos)]
  calc (Fintype.card Moves : ℝ)⁻¹
        * |∑ move : Moves,
            (model (move • input) - model (move • other_input))|
      ≤ (Fintype.card Moves : ℝ)⁻¹
        * ∑ move : Moves,
            |model (move • input) - model (move • other_input)| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (inv_pos.mpr count_pos).le
    _ ≤ (Fintype.card Moves : ℝ)⁻¹
        * ∑ _move : Moves, (slope_limit * dist input other_input) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun move _ => move_error_bound move)
          (inv_pos.mpr count_pos).le
    _ = slope_limit * dist input other_input := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ count_pos.ne', one_mul]

variable {Actions : Type*} [Fintype Actions] [DecidableEq Actions]

/-- **A baseline pushes nothing on average.** For a policy over actions, the
push on the score of action `chosen_action` from "action taken minus
prediction", averaged over the action taken, is zero. -/
theorem sum_mul_baseline_eq_zero
    {policy : Actions → ℝ}
    (policy_sums_to_one : ∑ i, policy i = 1)
    (chosen_action : Actions) :
    let average_push :=
      ∑ i, policy i *
        ((if i = chosen_action then 1 else 0) - policy chosen_action)  -- the push of a softmax policy: indicator minus its share
    let no_push : ℝ := 0
    average_push = no_push := by
  unfold_named_pieces
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, ← Finset.sum_mul,
    policy_sums_to_one, one_mul, sub_self]

/-- So subtracting a baseline from every reward leaves the average push as it
was. -/
theorem sum_mul_sub_baseline
    {policy : Actions → ℝ}
    (policy_sums_to_one : ∑ i, policy i = 1)
    (rewards : Actions → ℝ)
    (baseline : ℝ)
    (chosen_action : Actions) :
    let push_with_baseline :=
      ∑ i, policy i * (rewards i - baseline) *
        ((if i = chosen_action then 1 else 0) - policy chosen_action)
    let push_without_baseline :=
      ∑ i, policy i * rewards i *
        ((if i = chosen_action then 1 else 0) - policy chosen_action)
    push_with_baseline = push_without_baseline := by
  unfold_named_pieces
  -- The baseline's part is the baseline times a push that averages to zero.
  have baseline_part_zero :
      ∑ i, policy i *
        ((if i = chosen_action then 1 else 0) - policy chosen_action) = 0 :=
    sum_mul_baseline_eq_zero policy_sums_to_one chosen_action
  have split_term : ∀ i,
      policy i * (rewards i - baseline) *
          ((if i = chosen_action then 1 else 0) - policy chosen_action)
        = policy i * rewards i *
            ((if i = chosen_action then 1 else 0) - policy chosen_action)
          - baseline * (policy i *
            ((if i = chosen_action then 1 else 0) - policy chosen_action)) :=
    fun i => by ring
  simp only [split_term, Finset.sum_sub_distrib, ← Finset.mul_sum,
    baseline_part_zero, mul_zero, sub_zero]

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]

/-- Classifier-free guidance with strength `guidance_strength`:
`1 + guidance_strength` of the prediction with the prompt, minus
`guidance_strength` of the prediction without it.
Python: `(1 + strength) * with_prompt - strength * without_prompt`. -/
def APPLY_GUIDANCE
    (guidance_strength : ℝ)
    (without_prompt with_prompt : Space) : Space :=
  (1 + guidance_strength) • with_prompt - guidance_strength • without_prompt

/-- Guidance moves from the plain prediction in the direction of the prompt,
`1 + guidance_strength` times as far as the prompt alone does. -/
theorem guidance_sub
    (guidance_strength : ℝ)
    (without_prompt with_prompt : Space) :
    let guided_move :=
      APPLY_GUIDANCE guidance_strength without_prompt with_prompt
        - without_prompt
    let scaled_move :=
      (1 + guidance_strength) • (with_prompt - without_prompt)
    guided_move = scaled_move := by
  unfold_named_pieces
  rw [APPLY_GUIDANCE]
  module

/-- The guided step is `1 + guidance_strength` times as long as the plain
step. -/
theorem norm_guidance_sub
    {guidance_strength : ℝ}
    (strength_ok : 0 ≤ 1 + guidance_strength)
    (without_prompt with_prompt : Space) :
    let guided_length :=
      ‖APPLY_GUIDANCE guidance_strength without_prompt with_prompt
        - without_prompt‖
    let scaled_length :=
      (1 + guidance_strength) * ‖with_prompt - without_prompt‖
    guided_length = scaled_length := by
  unfold_named_pieces
  have guided_move_eq :
      APPLY_GUIDANCE guidance_strength without_prompt with_prompt
          - without_prompt
        = (1 + guidance_strength) • (with_prompt - without_prompt) :=
    guidance_sub guidance_strength without_prompt with_prompt
  rw [guided_move_eq, norm_smul, Real.norm_of_nonneg strength_ok]

/-- **Guidance is not an average.** For a positive strength the guided
prediction is not on the stretch between the two predictions it is made
from. -/
theorem guidance_notMem_segment
    {guidance_strength : ℝ}
    (strength_pos : 0 < guidance_strength)
    {without_prompt with_prompt : Space}
    (predictions_differ : with_prompt ≠ without_prompt) :
    let guided  :=
      APPLY_GUIDANCE guidance_strength without_prompt with_prompt
    let stretch := segment ℝ without_prompt with_prompt
    guided ∉ stretch := by
  unfold_named_pieces
  rintro ⟨without_share, with_share, without_share_nonneg, -,
    shares_sum_to_one, on_stretch⟩
  -- On the stretch the point is `without_prompt + with_share • (step)` with
  -- `with_share ≤ 1`; guidance has `1 + guidance_strength` there.
  have step_is_zero :
      (1 + guidance_strength - with_share) • (with_prompt - without_prompt)
        = 0 := by
    have without_share_eq : without_share = 1 - with_share := by linarith
    have guided_move_on_stretch :
        APPLY_GUIDANCE guidance_strength without_prompt with_prompt
            - without_prompt
          = with_share • (with_prompt - without_prompt) := by
      rw [← on_stretch, without_share_eq]
      module
    have guided_move_eq :
        APPLY_GUIDANCE guidance_strength without_prompt with_prompt
            - without_prompt
          = (1 + guidance_strength) • (with_prompt - without_prompt) :=
      guidance_sub guidance_strength without_prompt with_prompt
    rw [guided_move_eq] at guided_move_on_stretch
    rw [sub_smul, guided_move_on_stretch, sub_self]
  rcases smul_eq_zero.mp step_is_zero with factor_zero | difference_zero
  · have with_share_le_one : with_share ≤ 1 := by linarith
    linarith
  · exact predictions_differ (sub_eq_zero.mp difference_zero)

end SquigglyLine
