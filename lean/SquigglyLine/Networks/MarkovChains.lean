/-
A chain of Markov chains.

Training a deep network is a chain through the training steps, each link of
which runs a chain through the layers. Both chains are memoryless: the next
state depends only on the current one.

The inner chain (`RUN_LAYERS`), and what having no memory costs:
* `merged_stays_merged`  : two birds at the same place stay together;
* `card_image_runLayers_append_le` : the flock never spreads over more places;
* `dead_stays_dead`      : a state every layer fixes is never left.

The photon (`MAKE_PLATE_MATRIX`), a two-state Markov chain with real chance in
it:
* `plateMatrix_pow`      : after `plate_count` plates it is alive with
                           probability `pass_probability ^ plate_count` and
                           "absorbed" is never left.

The outer chain (`TAKE_GRADIENT_STEP`), with orthogonal features:
* `HAS_TIGHT_FEATURES.residual_iterate_gradientStep` : the error after
                           `step_count` steps is
                           `(1 - learning_rate * squared_length) ^ step_count`
                           times the error at the start;
* `HAS_TIGHT_FEATURES.residual_gradientStep_inv`     : with
                           `learning_rate = 1 / squared_length`, one step fits.

Definitions and theorems:

| Name                              | Meaning                               |
|-----------------------------------|---------------------------------------|
| `Layer`                           | one layer: a map from state to state  |
| `LayerStack`                      | a list of layers                      |
| `RUN_LAYERS`                      | run a stack of layers                 |
| `runLayers_append`                | running two stacks one after the other|
| `merged_stays_merged`             | two merged birds stay merged          |
| `card_image_runLayers_append_le`  | a flock never spreads                 |
| `dead_stays_dead`                 | a fixed state is never left           |
| `polarizer_zero`, `fan_zero`      | nothing in, nothing out               |
| `TransitionMatrix`                | a two-state transition matrix         |
| `MAKE_PLATE_MATRIX`               | the matrix of one plate               |
| `plateMatrix_row_sum`             | each row is a distribution            |
| `plateMatrix_pow`                 | many plates                           |
| `survival_eq_sq_length`           | survival is the length squared        |
-/
import Mathlib.LinearAlgebra.Matrix.Notation
import SquigglyLine.Networks.Kernel
import SquigglyLine.Networks.Polarizer
import SquigglyLine.Networks.ThreePolarizers

namespace SquigglyLine

/-! ### The inner chain: through the layers -/

/-- One layer: it sends each state to the next state.
Python: `Callable[[State], State]`. -/
abbrev Layer (State : Type*) := State → State

/-- A stack of layers. The head of the list is the first layer.
Python: `list[Layer]`. -/
abbrev LayerStack (State : Type*) := List (Layer State)

section Inner

variable {State : Type*}

/-- Run a stack of layers. The head of the list is the first layer. -/
def RUN_LAYERS : LayerStack State → State → State
  | [] => id
  | layer :: later_layers => RUN_LAYERS later_layers ∘ layer

/-- Running two stacks one after the other: first the early layers, then the
late ones. -/
theorem runLayers_append
    (early_layers : LayerStack State)
    (late_layers : LayerStack State) :
    let all_layers := early_layers ++ late_layers
    let run_all    := RUN_LAYERS all_layers
    let run_late_after_early :=
      RUN_LAYERS late_layers ∘ RUN_LAYERS early_layers
    run_all = run_late_after_early := by
  unfold_named_pieces
  induction early_layers with
  | nil => rfl
  | cons layer later_early_layers earlier_case =>
    simp only [List.cons_append, RUN_LAYERS, earlier_case,
      Function.comp_assoc]

/-- **Merged stays merged.** Two birds at the same place after some layers are
at the same place after any further layers. -/
theorem merged_stays_merged
    (early_layers : LayerStack State)
    (late_layers : LayerStack State)
    {bird : State}
    {other_bird : State}
    (merged_after_early :
      RUN_LAYERS early_layers bird = RUN_LAYERS early_layers other_bird) :
    let all_layers := early_layers ++ late_layers
    let place       := RUN_LAYERS all_layers bird
    let other_place := RUN_LAYERS all_layers other_bird
    place = other_place := by
  unfold_named_pieces
  have run_append :
      RUN_LAYERS (early_layers ++ late_layers)
        = RUN_LAYERS late_layers ∘ RUN_LAYERS early_layers :=
    runLayers_append early_layers late_layers
  simp only [run_append, Function.comp_apply, merged_after_early]

/-- **The flock never spreads over more places.** Further layers cannot
increase the number of distinct places a flock occupies. -/
theorem card_image_runLayers_append_le
    [DecidableEq State]
    (early_layers : LayerStack State)
    (late_layers : LayerStack State)
    (flock : Finset State) :
    let all_layers := early_layers ++ late_layers
    let places_after_all   := flock.image (RUN_LAYERS all_layers)
    let places_after_early := flock.image (RUN_LAYERS early_layers)
    let count_after_all    := places_after_all.card
    let count_after_early  := places_after_early.card
    count_after_all ≤ count_after_early := by
  unfold_named_pieces
  have run_append :
      RUN_LAYERS (early_layers ++ late_layers)
        = RUN_LAYERS late_layers ∘ RUN_LAYERS early_layers :=
    runLayers_append early_layers late_layers
  -- Running the late layers on the places after the early layers is one more
  -- map, and a map never creates new places.
  rw [run_append, ← Finset.image_image]
  exact Finset.card_image_le

/-- **Dead stays dead.** A state that every layer leaves alone is never
left. -/
theorem dead_stays_dead
    (layers : LayerStack State)
    {dead : State}
    (every_layer_fixes_dead : ∀ layer ∈ layers, layer dead = dead) :
    let final_state := RUN_LAYERS layers dead
    final_state = dead := by
  unfold_named_pieces
  induction layers with
  | nil => rfl
  | cons first_layer later_layers earlier_case =>
    rw [RUN_LAYERS, Function.comp_apply,
      every_layer_fixes_dead first_layer (List.mem_cons_self ..)]
    exact earlier_case fun layer layer_in_later =>
      every_layer_fixes_dead layer (List.mem_cons_of_mem _ layer_in_later)

/-- A blocked photon stays blocked. -/
theorem polarizer_zero
    (axis_angle : ℝ) :
    let blocked_light : LightArrow := (0, 0)
    let outgoing_light := PASS_THROUGH_POLARIZER axis_angle blocked_light
    outgoing_light = blocked_light := by
  unfold_named_pieces
  simp [PASS_THROUGH_POLARIZER]

/-- A bird at the origin stays at the origin under any fan. -/
theorem fan_zero
    (angle : ℝ) :
    let origin : PlanePoint := (0, 0)
    let bird_after_layer := APPLY_FAN angle origin
    bird_after_layer = origin := by
  unfold_named_pieces
  simp [APPLY_FAN, ROTATE, APPLY_RELU_TO_PAIR]

end Inner

/-! ### The photon: a two-state Markov chain -/

section Photon

/-- A transition matrix on two states: entry `(row, column)` is the chance of
going from state `row` to state `column`. -/
abbrev TransitionMatrix := Matrix (Fin 2) (Fin 2) ℝ

/-- The transition matrix of one plate. State 0 is "alive", state 1 is
"absorbed". An alive photon passes with probability `pass_probability`. -/
def MAKE_PLATE_MATRIX
    (pass_probability : ℝ) : TransitionMatrix :=
  !![pass_probability, 1 - pass_probability; 0, 1]  -- row 0: alive; row 1: absorbed stays absorbed

/-- Each row of the transition matrix is a probability distribution. -/
theorem plateMatrix_row_sum
    (pass_probability : ℝ)
    (state : Fin 2) :
    let plate_matrix := MAKE_PLATE_MATRIX pass_probability
    let row_total    := ∑ j, plate_matrix state j
    row_total = 1 := by
  unfold_named_pieces
  fin_cases state <;> simp [MAKE_PLATE_MATRIX, Fin.sum_univ_two]

/-- **The photon's chain.** After `plate_count` plates an alive photon is still
alive with probability `pass_probability ^ plate_count`, and an absorbed photon
is still absorbed. -/
theorem plateMatrix_pow
    (pass_probability : ℝ)
    (plate_count : ℕ) :
    let plate_matrix    := MAKE_PLATE_MATRIX pass_probability
    let matrix_after    := plate_matrix ^ plate_count
    let survival        := pass_probability ^ plate_count  -- the photon must pass every plate
    let expected_matrix : TransitionMatrix := !![survival, 1 - survival; 0, 1]
    matrix_after = expected_matrix := by
  unfold_named_pieces
  induction plate_count with
  | zero => simp [Matrix.one_fin_two]
  | succ earlier_plate_count earlier_case =>
    rw [pow_succ, earlier_case, MAKE_PLATE_MATRIX, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ]
    ring

/-- The survival probability is the square of the surviving length:
`(cos² angle) ^ plate_count` is `(cos angle ^ plate_count)²`. -/
theorem survival_eq_sq_length
    (angle : ℝ)
    (plate_count : ℕ) :
    let plate_matrix := MAKE_PLATE_MATRIX (Real.cos angle ^ 2)  -- Malus's law: probability is cos² of the angle
    let survival     := (plate_matrix ^ plate_count) 0 0
    let squared_length := (Real.cos angle ^ plate_count) ^ 2
    survival = squared_length := by
  unfold_named_pieces
  have power_form :
      MAKE_PLATE_MATRIX (Real.cos angle ^ 2) ^ plate_count
        = !![(Real.cos angle ^ 2) ^ plate_count,
            1 - (Real.cos angle ^ 2) ^ plate_count; 0, 1] :=
    plateMatrix_pow (Real.cos angle ^ 2) plate_count
  rw [power_form]
  simp [pow_right_comm]

end Photon

/-! ### The outer chain: through training -/

section Outer

open ContinuousLinearMap

variable {Weights Outputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]
  {predict : Weights →L[ℝ] Outputs} {squared_length : ℝ}

/-- **The outer chain, solved.** With orthogonal features of squared length
`squared_length`, the error after `step_count` gradient steps is
`(1 - learning_rate * squared_length) ^ step_count` times the error at the
start. -/
theorem HAS_TIGHT_FEATURES.residual_iterate_gradientStep
    (tight_features : HAS_TIGHT_FEATURES predict squared_length)
    (labels : Outputs)
    (learning_rate : ℝ)
    (weights : Weights)
    (step_count : ℕ) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count] weights
    let residual_after  := GET_RESIDUAL linear_predict labels trained_weights
    let residual_before := GET_RESIDUAL linear_predict labels weights
    let shrink_factor   :=
      (1 - learning_rate * squared_length) ^ step_count  -- each step keeps this fraction of the error
    residual_after = shrink_factor • residual_before := by
  unfold_named_pieces
  induction step_count with
  | zero => simp
  | succ earlier_step_count earlier_case =>
    -- One more step multiplies the error by `1 - learning_rate * squared_length`.
    rw [Function.iterate_succ_apply', residual_gradientStep, earlier_case,
      tight_features]
    module

/-- **One step fits.** With the step size `1 / squared_length`, a single
gradient step leaves no error. -/
theorem HAS_TIGHT_FEATURES.residual_gradientStep_inv
    (tight_features : HAS_TIGHT_FEATURES predict squared_length)
    (squared_length_ne_zero : squared_length ≠ 0)
    (labels : Outputs)
    (weights : Weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let stepped_weights :=
      TAKE_GRADIENT_STEP predict labels squared_length⁻¹ weights  -- step size 1 / squared_length
    let residual_after := GET_RESIDUAL linear_predict labels stepped_weights
    let no_error : Outputs := 0
    residual_after = no_error := by
  unfold_named_pieces
  have one_step_case :=
    tight_features.residual_iterate_gradientStep labels squared_length⁻¹
      weights 1
  simpa [inv_mul_cancel₀ squared_length_ne_zero] using one_step_case

end Outer

end SquigglyLine
