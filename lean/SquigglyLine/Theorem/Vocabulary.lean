/-
Vocabulary for reading the theorem like a short script.

Every name in this file is a second name for something defined elsewhere.
Nothing new is defined and nothing is proved. The names exist so that a
statement never shows a single letter, a Greek letter or a type inside a
type.

Three kinds of name, told apart by their case, as in Python:

* `PascalCase`            a type (`RealFunction`, `DataDistribution`).
* `SCREAMING_SNAKE_CASE`  a global: a constant (`PI`) or a function. A
                          function is named as a verb: `GET_...` returns a
                          value, `MAKE_...` builds an object, and `IS_...`,
                          `ARE_...` or `HOLDS_...` answers yes or no.
* `snake_case`            a local name that lives inside one statement
                          (`amplitude`, `frequency`, `nearest_distance`).

Each is an `abbrev`, so Lean sees straight through it: every lemma proved
about the old name applies to the new one unchanged. `HOLDS_FOR_EVERY_SINE`
is the one `def`, because it wraps a repeated "for every ..." and should
stay folded when a statement is printed.

| New name                           | It stands for                        |
|------------------------------------|--------------------------------------|
| `RealFunction`                     | `ℝ → ℝ`                              |
| `Warp`                             | `ℝ → ℝ`, "where each input is moved" |
| `DataDistribution`                 | `Measure (DataPoint ℝ)`              |
| `SinePhase`                        | `(sineWave A w).Param`               |
| `PI`                               | `Real.pi`, which Mathlib writes `π`  |
| `GET_LABEL data_point`             | `data_point.2`                       |
| `GET_NEAREST_DISTANCE`             | `nearestDist`                        |
| `GET_VERTICAL_ERROR`               | `verticalDist`                       |
| `GET_RESIDUAL_LOSS`                | `residualLoss`                       |
| `MAKE_RANDOM_PHASE_SINE`           | `sineWave`                           |
| `IS_IN_SINE_BAND A value`          | `value ∈ Set.Icc (-|A|) |A|`         |
| `ARE_LABELS_ALMOST_SURELY_IN_BAND` | `∀ᵐ p ∂μ, p.2 ∈ Set.Icc (-|A|) |A|`  |
| `GOES_TO_ZERO_AS_INPUT_GROWS`      | `Tendsto f atTop (𝓝 0)`              |
| `HOLDS_FOR_EVERY_SINE`             | `∀ w, 0 < w → ∀ φ, ...`              |
-/
import SquigglyLine.Theorem.RandomPhase

namespace SquigglyLine

open MeasureTheory Filter Topology

/-! ## Types -/

/-- A function from real numbers to real numbers.
Python: `Callable[[float], float]`. -/
abbrev RealFunction := ℝ → ℝ

/-- A rearrangement of the inputs: where each input is moved to.
Python: `Callable[[float], float]`. -/
abbrev Warp := ℝ → ℝ

/-- The data as a distribution: a way to draw `(x, y)` pairs at random.
Python: a sampler; a dataset with weight `1 / n` on each point is one. -/
abbrev DataDistribution := Measure (DataPoint ℝ)

/-! ## Constants -/

/-- The circle constant, 3.14159...
Python: `math.pi`. -/
noncomputable abbrev PI : ℝ := Real.pi

/-! ## Functions that return a value -/

/-- The label (the `y` part) of a data point.
Python: `data_point[1]`. -/
abbrev GET_LABEL (data_point : DataPoint ℝ) : ℝ := data_point.2

/-- The distance from a data point to the nearest point of the curve.
Python: `min(dist((x, y), (t, curve(t))) for t in all_reals)`. -/
noncomputable abbrev GET_NEAREST_DISTANCE : Cost ℝ := nearestDist

/-- The vertical error `|y - curve(x)|`.
Python: `abs(y - curve(x))`. -/
abbrev GET_VERTICAL_ERROR : Cost ℝ := verticalDist

/-- The loss of one data point: `loss_fn` applied to the residual
`y - curve(x)`.
Python: `loss_fn(y - curve(x))`. -/
abbrev GET_RESIDUAL_LOSS (loss_fn : RealFunction) : Cost ℝ :=
  residualLoss loss_fn

/-! ## Functions that build an object -/

/-- The sine `amplitude * sin(frequency * x + phase)`, with the phase drawn
uniformly at random.
Python: `phase = uniform(0, 2 * PI)`, then
`lambda x: amplitude * sin(frequency * x + phase)`. -/
noncomputable abbrev MAKE_RANDOM_PHASE_SINE (amplitude frequency : ℝ) :
    RandomFunction ℝ :=
  sineWave amplitude frequency

/-- The phase of a random-phase sine: a point on the circle.
Python: a float in `[0, 2 * PI)`, where `2 * PI` wraps round to `0`. -/
abbrev SinePhase (amplitude frequency : ℝ) : Type :=
  (MAKE_RANDOM_PHASE_SINE amplitude frequency).Param

/-! ## Functions that answer yes or no -/

/-- The value lies in the band a sine of this amplitude sweeps:
`[-|amplitude|, |amplitude|]`.
Python: `-abs(amplitude) <= value <= abs(amplitude)`. -/
abbrev IS_IN_SINE_BAND (amplitude value : ℝ) : Prop :=
  value ∈ Set.Icc (-|amplitude|) |amplitude|

/-- Almost every label lies in the band the sine sweeps: every label,
except for a set of data points that is drawn with probability zero.
Python: `all(IS_IN_SINE_BAND(amplitude, y) for (x, y) in data)`. -/
abbrev ARE_LABELS_ALMOST_SURELY_IN_BAND (amplitude : ℝ)
    (data_distribution : DataDistribution) : Prop :=
  ∀ᵐ data_point ∂data_distribution,
    IS_IN_SINE_BAND amplitude (GET_LABEL data_point)

/-- The quantity gets as close to zero as you like, once its input is large
enough.
Python: for every `tolerance > 0` there is a `threshold` with
`abs(quantity(input)) < tolerance` for every `input > threshold`. -/
abbrev GOES_TO_ZERO_AS_INPUT_GROWS (quantity : RealFunction) : Prop :=
  Tendsto quantity atTop (𝓝 0)

/-- The claim holds for every positive frequency and every phase.
Python: `all(claim(frequency, phase) for frequency in positive_reals
for phase in circle)`. -/
def HOLDS_FOR_EVERY_SINE (amplitude : ℝ)
    (claim : (frequency : ℝ) → SinePhase amplitude frequency → Prop) : Prop :=
  ∀ frequency : ℝ, 0 < frequency →
    ∀ phase : SinePhase amplitude frequency, claim frequency phase

end SquigglyLine
