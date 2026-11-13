/-
Vocabulary for reading the theorem like a short script.

Every name in this file is a second name for something defined elsewhere.
Nothing new is defined and nothing is proved. The names exist so that a
statement never shows a single letter, a Greek letter or a type inside a
type.

Three kinds of name, told apart by their case, as in Python:

* `PascalCase`            a type, or a yes-or-no statement about things
                          (`Dataset`, `SineBand`, `LabelsInBand`).
* `SCREAMING_SNAKE_CASE`  a global value or function, fixed once for the
                          whole project (`NEAREST_DIST`, `SINE_WAVE`).
* `snake_case`            a local name that lives inside one statement
                          (`amplitude`, `frequency`, `nearest_distance`).

Each is an `abbrev`, so Lean sees straight through it: every lemma proved
about the old name applies to the new one unchanged. `ForEverySine` is the
one `def`, because it wraps a repeated "for every ..." and should stay folded
when a statement is printed.

| New name                   | It stands for                                  |
|----------------------------|------------------------------------------------|
| `RealFunction`             | `ℝ → ℝ`                                        |
| `Warp`                     | `ℝ → ℝ`, read as "where each input is moved"   |
| `DataIndex n`              | `Fin n`                                        |
| `Dataset n`                | `Fin n → DataPoint ℝ`                          |
| `DataDistribution`         | `Measure (DataPoint ℝ)`                        |
| `PI`                       | `Real.pi`, which Mathlib writes `π`            |
| `LABEL_OF data_point`      | `data_point.2`                                 |
| `NEAREST_DIST`             | `nearestDist`                                  |
| `VERTICAL_DIST`            | `verticalDist`                                 |
| `RESIDUAL_LOSS`            | `residualLoss`                                 |
| `SINE_WAVE`                | `sineWave`                                     |
| `SineBand amplitude`       | `Set.Icc (-|amplitude|) |amplitude|`           |
| `SinePhase`                | `(sineWave amplitude frequency).Param`         |
| `LabelsInBand`             | `∀ i, (dataset i).2 ∈ Set.Icc ...`             |
| `LabelsAlmostSurelyInBand` | `∀ᵐ p ∂μ, p.2 ∈ Set.Icc ...`                   |
| `GoesToZeroAsInputGrows`   | `Tendsto f atTop (𝓝 0)`                        |
| `ForEverySine`             | `∀ w, 0 < w → ∀ φ, ...`                        |
-/
import SquigglyLine.Theorem.RandomPhase

namespace SquigglyLine

open MeasureTheory Filter Topology

/-! ## Plain types -/

/-- A function from real numbers to real numbers.
Python: `Callable[[float], float]`. -/
abbrev RealFunction := ℝ → ℝ

/-- A rearrangement of the inputs: where each input is moved to.
Python: `Callable[[float], float]`. -/
abbrev Warp := ℝ → ℝ

/-- Which data point: an index from `0` to `n - 1`.
Python: `range(n)`. -/
abbrev DataIndex (n : ℕ) := Fin n

/-- A dataset of `n` labelled examples `(x, y)`.
Python: `list[tuple[float, float]]` of length `n`. -/
abbrev Dataset (n : ℕ) := DataIndex n → DataPoint ℝ

/-- The data as a distribution: a way to draw `(x, y)` pairs at random.
Python: a sampler; a dataset with weight `1 / n` on each point is one. -/
abbrev DataDistribution := Measure (DataPoint ℝ)

/-! ## Global values and functions -/

/-- The circle constant, 3.14159...
Python: `math.pi`. -/
noncomputable abbrev PI : ℝ := Real.pi

/-- The label (the `y` part) of a data point.
Python: `data_point[1]`. -/
abbrev LABEL_OF (data_point : DataPoint ℝ) : ℝ := data_point.2

/-- The distance from a data point to the nearest point of the curve.
Python: `min(dist((x, y), (t, curve(t))) for t in all_reals)`. -/
noncomputable abbrev NEAREST_DIST : Cost ℝ := nearestDist

/-- The vertical error `|y - curve(x)|`.
Python: `abs(y - curve(x))`. -/
abbrev VERTICAL_DIST : Cost ℝ := verticalDist

/-- The cost that applies `loss_fn` to the residual `y - curve(x)`.
Python: `loss_fn(y - curve(x))`. -/
abbrev RESIDUAL_LOSS (loss_fn : RealFunction) : Cost ℝ := residualLoss loss_fn

/-- The sine `amplitude * sin(frequency * x + phase)`, with the phase drawn
uniformly at random.
Python: `phase = uniform(0, 2 * pi)`, then
`lambda x: amplitude * sin(frequency * x + phase)`. -/
noncomputable abbrev SINE_WAVE (amplitude frequency : ℝ) : RandomFunction ℝ :=
  sineWave amplitude frequency

/-! ## Types and statements about sines -/

/-- The values a sine of this amplitude sweeps: `[-|amplitude|, |amplitude|]`.
Python: `-abs(amplitude) <= value <= abs(amplitude)`. -/
abbrev SineBand (amplitude : ℝ) : Set ℝ := Set.Icc (-|amplitude|) |amplitude|

/-- The phase of a random-phase sine: a point on the circle.
Python: a float in `[0, 2 * pi)`, where `2 * pi` wraps round to `0`. -/
abbrev SinePhase (amplitude frequency : ℝ) : Type :=
  (SINE_WAVE amplitude frequency).Param

/-- Every label in the dataset lies inside the band the sine sweeps.
Python: `all(-abs(amplitude) <= y <= abs(amplitude) for (x, y) in dataset)`. -/
abbrev LabelsInBand (amplitude : ℝ) {n : ℕ} (dataset : Dataset n) : Prop :=
  ∀ i : DataIndex n, LABEL_OF (dataset i) ∈ SineBand amplitude

/-- Almost every label lies inside the band the sine sweeps: every label,
except for a set of data points that is drawn with probability zero. -/
abbrev LabelsAlmostSurelyInBand (amplitude : ℝ)
    (data_distribution : DataDistribution) : Prop :=
  ∀ᵐ data_point ∂data_distribution, LABEL_OF data_point ∈ SineBand amplitude

/-- The quantity gets as close to zero as you like, once its input is large
enough.
Python: for every `tolerance > 0` there is a `threshold` with
`abs(quantity(input)) < tolerance` for every `input > threshold`. -/
abbrev GoesToZeroAsInputGrows (quantity : RealFunction) : Prop :=
  Tendsto quantity atTop (𝓝 0)

/-- "For every positive frequency and every phase, the claim holds."
Python: `all(claim(frequency, phase) for frequency in positive_reals
for phase in circle)`. -/
def ForEverySine (amplitude : ℝ)
    (claim : (frequency : ℝ) → SinePhase amplitude frequency → Prop) : Prop :=
  ∀ frequency : ℝ, 0 < frequency →
    ∀ phase : SinePhase amplitude frequency, claim frequency phase

end SquigglyLine
