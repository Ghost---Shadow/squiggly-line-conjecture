/-
Residual layers: what a skip does to squiggle.

A residual layer is `input + branch input`. If the branch has slope at most
`slope_limit`, the layer has slope between `1 - slope_limit` and
`1 + slope_limit`. Three things follow.

* With `slope_limit < 1` no two inputs are merged, and with one input the
  layer is always rising: a residual layer adds a turn only where its branch
  is steeper than one.
* `layer_count` layers with branches of slope `exponent / layer_count` have
  total slope at most `e ^ exponent`, however deep.
* The memory cell of an LSTM is a skip through time with a gate on it: its
  slope per step is the forget gate, and exactly one with the gate open.

| Name                    | Meaning                                         |
|-------------------------|-------------------------------------------------|
| `ADD_SKIP`              | a residual layer: `input + branch input`        |
| `RUN_RESIDUAL_LAYERS`   | a stack of residual layers                      |
| `UPDATE_CELL`           | one step of the memory cell of an LSTM          |
| `RUN_CELL`              | the cell after several steps                    |

Theorems: `lipschitzWith_addSkip`, `le_dist_addSkip`, `addSkip_injective`,
`strictMono_addSkip`, `neverTurns_addSkip`, `one_add_div_pow_le_exp`,
`lipschitzWith_runResidualLayers`, `dist_runResidualLayers_le_exp`,
`abs_updateCell_sub`, `abs_updateCell_sub_le`, `updateCell_sub_of_open_gate`,
`runCell_sub`.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.MetricSpace.Lipschitz
import SquigglyLine.Networks.NarrowChain
import SquigglyLine.Theorem.Sandwich

namespace SquigglyLine

open NNReal

variable {Space : Type*} [NormedAddCommGroup Space]
  {branch : Space → Space} {slope_limit : SlopeLimit}

/-- A residual layer: the input, plus what the branch makes of it.
Python: `input + branch(input)`. -/
def ADD_SKIP
    (branch : Space → Space)
    (input : Space) : Space :=
  input + branch input

/-- A residual layer is no steeper than one plus its branch. -/
theorem lipschitzWith_addSkip
    (slope_is_bounded : LipschitzWith slope_limit branch) :
    let layer_slope_limit := 1 + slope_limit  -- the input passes through, the branch adds its own slope
    let layer             := ADD_SKIP branch
    LipschitzWith layer_slope_limit layer := by
  unfold_named_pieces
  refine LipschitzWith.of_dist_le_mul fun input other_input => ?_
  have branch_gap := slope_is_bounded.dist_le_mul input other_input
  calc dist (input + branch input) (other_input + branch other_input)
      ≤ dist input other_input
          + dist (branch input) (branch other_input) :=
        dist_add_add_le _ _ _ _
    _ ≤ dist input other_input + slope_limit * dist input other_input := by
        gcongr
    _ = ((1 + slope_limit : ℝ≥0) : ℝ) * dist input other_input := by
        push_cast; ring

/-- **A skip keeps points apart.** Two outputs are at least `1 - slope_limit`
of the distance between their inputs. -/
theorem le_dist_addSkip
    (slope_is_bounded : LipschitzWith slope_limit branch)
    (input : Space)
    (other_input : Space) :
    let kept_share : ℝ := 1 - slope_limit  -- the skip keeps all, the branch can undo at most `slope_limit`
    let input_gap      := dist input other_input
    let output_gap     := dist (ADD_SKIP branch input)
                          (ADD_SKIP branch other_input)
    kept_share * input_gap ≤ output_gap := by
  unfold_named_pieces
  have norm_step := norm_sub_norm_le (input - other_input)
    (branch other_input - branch input)
  have same_difference :
      input - other_input - (branch other_input - branch input)
        = input + branch input - (other_input + branch other_input) := by
    abel
  have branch_gap_le :
      ‖branch other_input - branch input‖
        ≤ slope_limit * ‖input - other_input‖ := by
    have step := slope_is_bounded.dist_le_mul other_input input
    rwa [dist_eq_norm, dist_eq_norm, norm_sub_rev other_input input] at step
  rw [same_difference] at norm_step
  simp only [ADD_SKIP, dist_eq_norm]
  linarith

/-- With a branch of slope below one, a residual layer never merges two
inputs. -/
theorem addSkip_injective
    (slope_is_bounded : LipschitzWith slope_limit branch)
    (slope_limit_lt_one : slope_limit < 1) :
    let layer := ADD_SKIP branch
    Function.Injective layer := by
  unfold_named_pieces
  intro input other_input same_output
  have gap_le := le_dist_addSkip slope_is_bounded input other_input
  rw [same_output, dist_self] at gap_le
  have slope_limit_lt_one' : (slope_limit : ℝ) < 1 := by
    exact_mod_cast slope_limit_lt_one
  have gap_nonpos : dist input other_input ≤ 0 := by
    nlinarith [dist_nonneg (x := input) (y := other_input)]
  exact dist_le_zero.mp gap_nonpos

/-- With one input and a branch of slope below one, a residual layer is always
rising. -/
theorem strictMono_addSkip
    {branch : RealFunction}
    (slope_is_bounded : LipschitzWith slope_limit branch)
    (slope_limit_lt_one : slope_limit < 1) :
    let layer := ADD_SKIP branch
    StrictMono layer := by
  unfold_named_pieces
  intro input other_input input_lt_other
  have branch_gap := slope_is_bounded.dist_le_mul input other_input
  rw [Real.dist_eq, Real.dist_eq,
    abs_of_neg (sub_neg.mpr input_lt_other)] at branch_gap
  have branch_le_abs :
      branch input - branch other_input
        ≤ |branch input - branch other_input| := le_abs_self _
  have slope_limit_lt_one' : (slope_limit : ℝ) < 1 := by
    exact_mod_cast slope_limit_lt_one
  have slope_gap_lt :
      (slope_limit : ℝ) * (other_input - input) < 1 * (other_input - input) :=
    mul_lt_mul_of_pos_right slope_limit_lt_one' (sub_pos.mpr input_lt_other)
  show input + branch input < other_input + branch other_input
  linarith

/-- **A turn has to be bought in the branch.** With a branch of slope below
one, a residual layer never turns. -/
theorem neverTurns_addSkip
    {branch : RealFunction}
    (slope_is_bounded : LipschitzWith slope_limit branch)
    (slope_limit_lt_one : slope_limit < 1) :
    let layer := ADD_SKIP branch
    NEVER_TURNS layer := by
  unfold_named_pieces
  exact Or.inl (strictMono_addSkip slope_is_bounded slope_limit_lt_one).monotone

/-- `(1 + exponent / layer_count) ^ layer_count` never passes
`e ^ exponent`. -/
theorem one_add_div_pow_le_exp
    {exponent : ℝ}
    (exponent_nonneg : 0 ≤ exponent)
    (layer_count : ℕ) :
    let layer_growth := 1 + exponent / layer_count  -- each layer grows by its share of the exponent
    let stack_growth := layer_growth ^ layer_count
    let exp_growth   := Real.exp exponent
    stack_growth ≤ exp_growth := by
  unfold_named_pieces
  rcases Nat.eq_zero_or_pos layer_count with rfl | layer_count_pos
  · simpa using Real.one_le_exp exponent_nonneg
  · have share_nonneg : 0 ≤ exponent / layer_count :=
      div_nonneg exponent_nonneg (Nat.cast_nonneg layer_count)
    have layer_count_ne_zero : (layer_count : ℝ) ≠ 0 := by
      exact_mod_cast layer_count_pos.ne'
    -- `1 + x ≤ exp x`, raised to the power `layer_count`.
    calc (1 + exponent / layer_count) ^ layer_count
        ≤ (Real.exp (exponent / layer_count)) ^ layer_count :=
          pow_le_pow_left₀ (by linarith)
            (by linarith [Real.add_one_le_exp (exponent / layer_count)])
            layer_count
      _ = Real.exp exponent := by
          rw [← Real.exp_nat_mul]
          congr 1
          field_simp

/-- A stack of residual layers: layer `layer_index` adds
`branches layer_index` of what the layers below made.
Python: `for i in range(layer_count): x = x + branches[i](x)`. -/
def RUN_RESIDUAL_LAYERS
    (branches : ℕ → Space → Space) : ℕ → Space → Space
  | 0 => id
  | layer_index + 1 =>
    ADD_SKIP (branches layer_index) ∘ RUN_RESIDUAL_LAYERS branches layer_index

/-- `layer_count` residual layers with branches of slope at most
`slope_limit` have slope at most `(1 + slope_limit) ^ layer_count`. -/
theorem lipschitzWith_runResidualLayers
    {branches : ℕ → Space → Space}
    (slopes_are_bounded :
      ∀ layer_index, LipschitzWith slope_limit (branches layer_index))
    (layer_count : ℕ) :
    let stack_slope_limit := (1 + slope_limit) ^ layer_count  -- every layer can add `1 + slope_limit`
    let stack             := RUN_RESIDUAL_LAYERS branches layer_count
    LipschitzWith stack_slope_limit stack := by
  unfold_named_pieces
  induction layer_count with
  | zero => simpa [RUN_RESIDUAL_LAYERS] using LipschitzWith.id
  | succ layer_count earlier_layers_bounded =>
    have layer_step : LipschitzWith (1 + slope_limit)
        (ADD_SKIP (branches layer_count)) :=
      lipschitzWith_addSkip (slopes_are_bounded layer_count)
    have composed := layer_step.comp earlier_layers_bounded
    rwa [← pow_succ'] at composed

/-- **Depth does not blow up the slope.** If each of `layer_count` branches has
slope at most `exponent / layer_count`, the whole stack has slope at most
`e ^ exponent`, whatever `layer_count` is. -/
theorem dist_runResidualLayers_le_exp
    {branches : ℕ → Space → Space}
    {exponent : ℝ≥0}
    {layer_count : ℕ}
    (slopes_are_bounded :
      ∀ layer_index,
        LipschitzWith (exponent / layer_count) (branches layer_index))
    (input : Space)
    (other_input : Space) :
    let stack        := RUN_RESIDUAL_LAYERS branches layer_count
    let output_gap   := dist (stack input) (stack other_input)
    let input_gap    := dist input other_input
    let growth_limit := Real.exp exponent  -- the most that `layer_count` layers can stretch a gap
    output_gap ≤ growth_limit * input_gap := by
  unfold_named_pieces
  have stack_gap := (lipschitzWith_runResidualLayers slopes_are_bounded
    layer_count).dist_le_mul input other_input
  have growth_bound :
      (((1 + exponent / layer_count : ℝ≥0) ^ layer_count : ℝ≥0) : ℝ)
        ≤ Real.exp exponent := by
    push_cast
    exact one_add_div_pow_le_exp exponent.coe_nonneg layer_count
  exact stack_gap.trans (mul_le_mul_of_nonneg_right growth_bound dist_nonneg)

/-- One step of the memory cell of an LSTM: keep the share `forget_gate` of the
cell, and add the share `input_gate` of the `candidate`.
Python: `forget_gate * cell + input_gate * candidate`. -/
def UPDATE_CELL
    (forget_gate : ℝ)
    (input_gate : ℝ)
    (candidate : ℝ)
    (cell : ℝ) : ℝ :=
  forget_gate * cell + input_gate * candidate

/-- **The slope of the cell is the forget gate.** -/
theorem abs_updateCell_sub
    {forget_gate : ℝ}
    (forget_gate_nonneg : 0 ≤ forget_gate)
    (input_gate : ℝ)
    (candidate : ℝ)
    (cell : ℝ)
    (other_cell : ℝ) :
    let new_gap := |UPDATE_CELL forget_gate input_gate candidate cell
                    - UPDATE_CELL forget_gate input_gate candidate other_cell|
    let old_gap := |cell - other_cell|
    new_gap = forget_gate * old_gap := by
  unfold_named_pieces
  -- The candidate term is the same in both and cancels.
  rw [UPDATE_CELL, UPDATE_CELL,
    show forget_gate * cell + input_gate * candidate
        - (forget_gate * other_cell + input_gate * candidate)
        = forget_gate * (cell - other_cell) by ring,
    abs_mul, abs_of_nonneg forget_gate_nonneg]

/-- A gate between zero and one never makes two memories differ by more. -/
theorem abs_updateCell_sub_le
    {forget_gate : ℝ}
    (forget_gate_nonneg : 0 ≤ forget_gate)
    (forget_gate_le_one : forget_gate ≤ 1)
    (input_gate : ℝ)
    (candidate : ℝ)
    (cell : ℝ)
    (other_cell : ℝ) :
    let new_gap := |UPDATE_CELL forget_gate input_gate candidate cell
                    - UPDATE_CELL forget_gate input_gate candidate other_cell|
    let old_gap := |cell - other_cell|
    new_gap ≤ old_gap := by
  unfold_named_pieces
  have gap_eq :
      |UPDATE_CELL forget_gate input_gate candidate cell
        - UPDATE_CELL forget_gate input_gate candidate other_cell|
        = forget_gate * |cell - other_cell| :=
    abs_updateCell_sub forget_gate_nonneg input_gate candidate cell other_cell
  rw [gap_eq]
  exact mul_le_of_le_one_left (abs_nonneg _) forget_gate_le_one

/-- **With the gate open the cell is a skip through time.** The difference
between two memories is carried forward unchanged. -/
theorem updateCell_sub_of_open_gate
    (input_gate : ℝ)
    (candidate : ℝ)
    (cell : ℝ)
    (other_cell : ℝ) :
    let new_gap := UPDATE_CELL 1 input_gate candidate cell
                   - UPDATE_CELL 1 input_gate candidate other_cell
    let old_gap := cell - other_cell
    new_gap = old_gap := by
  unfold_named_pieces
  rw [UPDATE_CELL, UPDATE_CELL]
  ring

/-- The cell after `step_count` steps, with the gates and candidates of each
step given. -/
def RUN_CELL
    (forget_gates : ℕ → ℝ)
    (input_gates : ℕ → ℝ)
    (candidates : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0, cell => cell
  | step + 1, cell =>
    UPDATE_CELL (forget_gates step) (input_gates step) (candidates step)
      (RUN_CELL forget_gates input_gates candidates step cell)

/-- After `step_count` steps the difference between two memories has been
multiplied by every forget gate on the way. -/
theorem runCell_sub
    (forget_gates : ℕ → ℝ)
    (input_gates : ℕ → ℝ)
    (candidates : ℕ → ℝ)
    (step_count : ℕ)
    (cell : ℝ)
    (other_cell : ℝ) :
    let new_gap     :=
      RUN_CELL forget_gates input_gates candidates step_count cell
        - RUN_CELL forget_gates input_gates candidates step_count other_cell
    let all_forgets := ∏ i ∈ Finset.range step_count, forget_gates i
    let old_gap     := cell - other_cell
    new_gap = all_forgets * old_gap := by
  unfold_named_pieces
  induction step_count with
  | zero => simp [RUN_CELL]
  | succ step_count earlier_steps =>
    rw [RUN_CELL, RUN_CELL, UPDATE_CELL, UPDATE_CELL,
      Finset.prod_range_succ]
    linear_combination forget_gates step_count * earlier_steps

end SquigglyLine
