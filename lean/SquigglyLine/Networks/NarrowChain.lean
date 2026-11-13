/-
The tunnel that cannot turn.

A ReLU network with one neuron per layer,

    relu(weight_1 * relu(weight_2 * relu(weight_3 * x + bias_3) + bias_2)
      + bias_1),

never turns, at any depth: its output only rises with the input, or only
falls. Each layer is monotone, and a chain of monotone maps is monotone.
In one dimension the only rotation is the full flip, so there is nothing to
turn through.

| Name                 | Meaning                                           |
|----------------------|---------------------------------------------------|
| `NarrowLayer`        | one neuron: a pair `(weight, bias)`               |
| `NarrowNetwork`      | a list of such layers, last layer first           |
| `APPLY_NARROW_LAYER` | `relu(weight * input + bias)`                     |
| `RUN_NARROW_CHAIN`   | the whole network, as a function of its input     |
| `NEVER_TURNS`        | the function only rises, or only falls            |

Theorems: `narrowLayer_neverTurns`, `NEVER_TURNS.comp`,
`narrowChain_neverTurns`, `NEVER_TURNS.between`.

How to read the notation:

* `max value 0` is ReLU. Python: `max(value, 0)`.
* `layer.1` and `layer.2` are the two parts of a pair. Python: `layer[0]`
  and `layer[1]`.
* `outer ∘ inner` is "first `inner`, then `outer`". Python:
  `lambda x: outer(inner(x))`.
-/
import Mathlib.Analysis.Normed.Module.Basic
import SquigglyLine.Style

namespace SquigglyLine

/-! ## Types -/

/-- One layer with a single neuron: its weight and its bias.
Python: `tuple[float, float]`. -/
abbrev NarrowLayer := ℝ × ℝ

/-- A network with one neuron per layer: the list of its layers. The head of
the list is the last layer.
Python: `list[NarrowLayer]`. -/
abbrev NarrowNetwork := List NarrowLayer

/-! ## The network -/

/-- A layer with a single neuron: `relu(weight * input + bias)`.
Python: `max(weight * input + bias, 0)`. -/
def APPLY_NARROW_LAYER
    (weight : ℝ)
    (bias : ℝ)
    (input : ℝ) : ℝ :=
  let before_relu := weight * input + bias
  max before_relu 0  -- ReLU: a negative value becomes 0

/-- A network with one neuron per layer. The head of the list is the last
layer.

    def RUN_NARROW_CHAIN(layers):
        if not layers:
            return lambda x: x
        (weight, bias), earlier_layers = layers[0], layers[1:]
        return lambda x: APPLY_NARROW_LAYER(
            weight, bias, RUN_NARROW_CHAIN(earlier_layers)(x))
-/
def RUN_NARROW_CHAIN
    (layers : NarrowNetwork) : RealFunction :=
  match layers with
  | [] => id  -- no layers: the input comes out unchanged
  | last_layer :: earlier_layers =>
    let weight := last_layer.1
    let bias   := last_layer.2
    APPLY_NARROW_LAYER weight bias ∘ RUN_NARROW_CHAIN earlier_layers  -- the earlier layers run first

/-- A function that never turns: it only rises, or it only falls.
Python, for any inputs listed in rising order:
`outputs == sorted(outputs) or outputs == sorted(outputs, reverse=True)`. -/
def NEVER_TURNS
    (model : RealFunction) : Prop :=
  let only_rises := Monotone model  -- a larger input never gives a smaller output
  let only_falls := Antitone model  -- a larger input never gives a larger output
  only_rises ∨ only_falls

/-! ## No layer turns, so no chain of layers turns -/

/-- A single one-neuron layer never turns. -/
theorem narrowLayer_neverTurns
    (weight : ℝ)
    (bias : ℝ) :
    let layer := APPLY_NARROW_LAYER weight bias
    NEVER_TURNS layer := by
  unfold_named_pieces
  -- A weight that is not negative keeps the order of two inputs. A weight
  -- that is not positive reverses it. Adding the bias and applying ReLU
  -- keep whatever order there is.
  exact (le_total 0 weight).elim
    (fun weight_nonneg => .inl fun _ _ input_le_other =>
      max_le_max
        (add_le_add_left
          (mul_le_mul_of_nonneg_left input_le_other weight_nonneg) bias)
        le_rfl)
    (fun weight_nonpos => .inr fun _ _ input_le_other =>
      max_le_max
        (add_le_add_left
          (mul_le_mul_of_nonpos_left input_le_other weight_nonpos) bias)
        le_rfl)

/-- Chaining two functions that never turn gives a function that never
turns. -/
theorem NEVER_TURNS.comp
    {outer : RealFunction}
    {inner : RealFunction}
    (outer_never_turns : NEVER_TURNS outer)
    (inner_never_turns : NEVER_TURNS inner) :
    let chained := outer ∘ inner  -- first `inner`, then `outer`
    NEVER_TURNS chained := by
  unfold_named_pieces
  -- Four cases. Rising after rising rises, and so does falling after
  -- falling: two flips cancel. One of each falls.
  rcases outer_never_turns with outer_rises | outer_falls <;>
    rcases inner_never_turns with inner_rises | inner_falls
  · exact .inl (outer_rises.comp inner_rises)
  · exact .inr (outer_rises.comp_antitone inner_falls)
  · exact .inr (outer_falls.comp_monotone inner_rises)
  · exact .inl (outer_falls.comp inner_falls)

/-- **A one-neuron-per-layer network never turns**, whatever its depth and
weights. -/
theorem narrowChain_neverTurns
    (layers : NarrowNetwork) :
    let network := RUN_NARROW_CHAIN layers
    NEVER_TURNS network := by
  unfold_named_pieces
  induction layers with
  | nil => exact .inl monotone_id
  | cons last_layer earlier_layers earlier_layers_never_turn =>
    -- The last layer never turns, and neither does everything before it.
    exact (narrowLayer_neverTurns last_layer.1 last_layer.2).comp
      earlier_layers_never_turn

/-- What "never turns" means for three inputs in a row: the middle output
lies between the outer two. There is no peak and no valley. -/
theorem NEVER_TURNS.between
    {model : RealFunction}
    (model_never_turns : NEVER_TURNS model)
    {left_input : ℝ}
    {middle_input : ℝ}
    {right_input : ℝ}
    (left_le_middle : left_input ≤ middle_input)
    (middle_le_right : middle_input ≤ right_input) :
    let left_output   := model left_input
    let middle_output := model middle_input
    let right_output  := model right_input
    let lower_end     := min left_output right_output
    let higher_end    := max left_output right_output
    let is_no_valley  := lower_end ≤ middle_output   -- the middle does not dip below both ends
    let is_no_peak    := middle_output ≤ higher_end  -- the middle does not rise above both ends
    is_no_valley ∧ is_no_peak := by
  unfold_named_pieces
  rcases model_never_turns with model_rises | model_falls
  · -- Rising: the middle is at least the left end and at most the right.
    exact ⟨(min_le_left _ _).trans (model_rises left_le_middle),
      (model_rises middle_le_right).trans (le_max_right _ _)⟩
  · -- Falling: the middle is at least the right end and at most the left.
    exact ⟨(min_le_right _ _).trans (model_falls middle_le_right),
      (model_falls left_le_middle).trans (le_max_left _ _)⟩

end SquigglyLine
