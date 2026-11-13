/-
Vocabulary for reading the theorem like a short script.

Every name in this file is a second name for something Mathlib already has.
Nothing new is defined and nothing is proved. The names exist so that a
statement never shows a type inside a type or a piece of Mathlib notation
that needs a course to read.

Each is an `abbrev`, so Lean sees straight through it: every lemma proved
about the thing itself applies to the name unchanged.

| Name                          | It stands for                           |
|-------------------------------|-----------------------------------------|
| `WarpOver Inputs`             | `Inputs → Inputs`, "where each input is moved" |
| `Warp`                        | `ℝ → ℝ`, the same for real inputs       |
| `DataDistributionOver Inputs` | `Measure (DataPoint Inputs)`            |
| `DataDistribution`            | `Measure (DataPoint ℝ)`                 |
| `GOES_TO_ZERO_AS_INPUT_GROWS` | `Tendsto quantity atTop (𝓝 0)`          |

`RealFunction` and `PI` are in `SquigglyLine/Style.lean`. `Model`,
`DataPoint`, `GET_INPUT` and `GET_LABEL` are in `Defs.lean`. The names that
are about sines are in `RandomPhase.lean`.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import SquigglyLine.Theorem.Defs

namespace SquigglyLine

open MeasureTheory Filter Topology

/-- A rearrangement of the inputs: where each input is moved to.
Python: `Callable[[Input], Input]`. -/
abbrev WarpOver (Inputs : Type*) := Inputs → Inputs

/-- A rearrangement of the inputs, when the inputs are real numbers.
Python: `Callable[[float], float]`. -/
abbrev Warp := WarpOver ℝ

/-- The data as a distribution: a way to draw `(input, label)` pairs at
random.
Python: a sampler; a dataset with weight `1 / n` on each point is one. -/
abbrev DataDistributionOver (Inputs : Type*) [MeasurableSpace Inputs] :=
  Measure (DataPoint Inputs)

/-- The data as a distribution, when the inputs are real numbers. -/
abbrev DataDistribution := DataDistributionOver ℝ

/-- The quantity gets as close to zero as you like, once its input is large
enough.
Python: for every `tolerance > 0` there is a `threshold` with
`abs(quantity(input)) < tolerance` for every `input > threshold`. -/
abbrev GOES_TO_ZERO_AS_INPUT_GROWS (quantity : RealFunction) : Prop :=
  Tendsto quantity atTop (𝓝 0)

end SquigglyLine
