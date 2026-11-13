/-
Vocabulary of the squiggly line conjecture.

A network computes a function from inputs to real numbers: a `Model`. Its
graph is the "squiggly line". A data point is a pair `(input, label)`. Two
costs compare the two:

* `GET_NEAREST_DISTANCE`  distance from the data point to the nearest point
                          of the line. This is the loss of the conjecture.
* `GET_RESIDUAL_LOSS`     any loss that reads only the residual
                          `label - model(input)`. This is what regression
                          trains on. `GET_VERTICAL_ERROR` is the case `|·|`.

| Name                   | Meaning                                         |
|------------------------|-------------------------------------------------|
| `Model Inputs`         | a function from inputs to real numbers          |
| `DataPoint Inputs`     | a pair `(input, label)`                         |
| `Cost Inputs`          | a number charged to a model on one data point   |
| `GET_INPUT`            | the input of a data point                       |
| `GET_LABEL`            | the label of a data point                       |
| `GET_RESIDUAL_LOSS`    | a loss applied to `label - model(input)`        |
| `GET_VERTICAL_ERROR`   | `|label - model(input)|`                        |
| `Ambient Inputs`       | the space the line and the data are drawn in    |
| `EMBED_DATA_POINT`     | a data point, placed in that space              |
| `GET_GRAPH`            | the squiggly line: every `(input, model(input))`|
| `GET_NEAREST_DISTANCE` | distance from a data point to the line          |

Theorems: `footpoint_mem_curve`, `embed_mem_curve_iff`, `dist_embed`.
-/
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Topology.MetricSpace.HausdorffDistance
import SquigglyLine.Style

namespace SquigglyLine

/-! ## Types -/

/-- A model: a function from inputs to real numbers.
Python: `Callable[[Input], float]`. -/
abbrev Model (Inputs : Type*) := Inputs → ℝ

/-- A labelled example: an input and its real label.
Python: `tuple[Input, float]`. -/
abbrev DataPoint (Inputs : Type*) := Inputs × ℝ

/-- A cost charged to a model on one data point.
Python: `Callable[[Model, DataPoint], float]`. -/
abbrev Cost (Inputs : Type*) := Model Inputs → DataPoint Inputs → ℝ

/-! ## Reading a data point

Both are marked `@[simp]`, so the simplifier replaces them by the plain
first and second parts of the pair wherever a proof needs that. -/

/-- The input (the `x` part) of a data point.
Python: `data_point[0]`. -/
@[simp] abbrev GET_INPUT {Inputs : Type*} (data_point : DataPoint Inputs) : Inputs :=
  data_point.1

/-- The label (the `y` part) of a data point.
Python: `data_point[1]`. -/
@[simp] abbrev GET_LABEL {Inputs : Type*} (data_point : DataPoint Inputs) : ℝ :=
  data_point.2

/-! ## The cost that training sees -/

/-- A loss that reads only the residual `label - model(input)`. Every
regression loss has this form.
Python: `loss_fn(label - model(input))`. -/
def GET_RESIDUAL_LOSS {Inputs : Type*} (loss_fn : RealFunction) : Cost Inputs :=
  fun model data_point =>
    let residual := GET_LABEL data_point - model (GET_INPUT data_point)
    loss_fn residual

/-- The vertical distance `|label - model(input)|` from a data point to the
line.
Python: `abs(label - model(input))`. -/
abbrev GET_VERTICAL_ERROR {Inputs : Type*} : Cost Inputs :=
  GET_RESIDUAL_LOSS abs

/-! ## The line, as a set of points -/

/-- The Euclidean space in which the line and the data live: the plane, when
the inputs are real numbers. -/
abbrev Ambient (Inputs : Type*) := WithLp 2 (Inputs × ℝ)

/-- A data point, placed in the ambient Euclidean space. -/
abbrev EMBED_DATA_POINT {Inputs : Type*} (data_point : DataPoint Inputs) :
    Ambient Inputs :=
  WithLp.toLp 2 data_point

/-- The squiggly line: the graph of the model.
Python: `{(input, model(input)) for input in all_inputs}`. -/
def GET_GRAPH {Inputs : Type*} (model : Model Inputs) : Set (Ambient Inputs) :=
  Set.range fun input => EMBED_DATA_POINT (input, model input)

/-- The point of the line directly above or below a data point. -/
theorem footpoint_mem_curve {Inputs : Type*}
    (model : Model Inputs)
    (data_point : DataPoint Inputs) :
    let input     := GET_INPUT data_point
    let footpoint := EMBED_DATA_POINT (input, model input)  -- same input, the model's own output
    footpoint ∈ GET_GRAPH model :=
  ⟨data_point.1, rfl⟩

/-- A data point is on the line exactly when its label is the model's
output. -/
theorem embed_mem_curve_iff {Inputs : Type*}
    (model : Model Inputs)
    (data_point : DataPoint Inputs) :
    let is_on_the_line :=
      EMBED_DATA_POINT data_point ∈ GET_GRAPH model
    let label_is_the_output :=
      GET_LABEL data_point = model (GET_INPUT data_point)
    is_on_the_line ↔ label_is_the_output := by
  unfold_named_pieces
  constructor
  · rintro ⟨input, input_gives_the_point⟩
    rw [← (WithLp.toLp_injective 2) input_gives_the_point]
  · intro label_is_the_output
    exact ⟨data_point.1,
      congrArg EMBED_DATA_POINT (Prod.ext rfl label_is_the_output.symm)⟩

/-! ## The cost of the conjecture -/

section Geometry

variable {Inputs : Type*} [SeminormedAddCommGroup Inputs]

/-- The Euclidean distance from a data point to the nearest point of the
line.
Python: `min(dist(data_point, point) for point in GET_GRAPH(model))`. -/
noncomputable def GET_NEAREST_DISTANCE : Cost Inputs :=
  fun model data_point =>
    Metric.infDist (EMBED_DATA_POINT data_point) (GET_GRAPH model)

/-- Pythagoras, for two data points in the ambient space. -/
theorem dist_embed
    (data_point other_point : DataPoint Inputs) :
    let distance :=
      dist (EMBED_DATA_POINT data_point) (EMBED_DATA_POINT other_point)
    let gap_in_input :=
      dist (GET_INPUT data_point) (GET_INPUT other_point)
    let gap_in_label :=
      dist (GET_LABEL data_point) (GET_LABEL other_point)
    distance = √(gap_in_input ^ 2 + gap_in_label ^ 2) :=  -- Pythagoras: the two gaps are at right angles
  WithLp.prod_dist_eq_of_L2 _ _

end Geometry

end SquigglyLine
