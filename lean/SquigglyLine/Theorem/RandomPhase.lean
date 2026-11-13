/-
Waves with a random phase.

`MAKE_RANDOM_PHASE_WAVE profile _ frequency` is the random model
`input ↦ profile(frequency * input + phase)`, where `profile` is any shape
that repeats with a fixed period and the phase is drawn uniformly from the
circle. With `profile = amplitude * sin` this is the curve family of
`scripts/frequency_isolation.py`.

The frequency changes how squiggly the wave is. It does not change the
one-point marginal, because a uniform phase stays uniform after a shift.

| Name                               | Meaning                               |
|------------------------------------|---------------------------------------|
| `Profile period`                   | one period of a wave                  |
| `MAKE_RANDOM_PHASE_WAVE`           | that wave, with a random phase        |
| `MAKE_RANDOM_PHASE_SINE`           | `amplitude * sin`, with a random phase|
| `SinePhase`                        | the type of the sine's phase          |
| `GET_SINE_BAND amplitude`          | the values a sine sweeps              |
| `IS_IN_SINE_BAND amplitude value`  | the value is one of them              |
| `ARE_LABELS_ALMOST_SURELY_IN_BAND` | the data's labels are in the band     |
| `HOLDS_FOR_EVERY_SINE`             | for every frequency > 0 and phase     |

Theorems: `marginal_randomPhaseWave`, `marginal_randomPhaseWave_eq`,
`continuous_circleSin`, `marginal_sineWave_eq`.
-/
import Mathlib.Analysis.Fourier.AddCircle
import SquigglyLine.Theorem.RandomFunction

namespace SquigglyLine

open MeasureTheory

/-- One period of a wave: a function on the circle of circumference
`period`.
Python: a function `f` with `f(angle + period) == f(angle)`. -/
abbrev Profile (period : ℝ) := AddCircle period → ℝ

variable {period : ℝ} [Fact (0 < period)] {profile : Profile period}

/-- The wave `input ↦ profile(frequency * input + phase)` with a uniformly
random phase.

    phase = uniform(0, period)
    wave = lambda input: profile(frequency * input + phase)
-/
noncomputable def MAKE_RANDOM_PHASE_WAVE
    (profile : Profile period)
    (profile_is_measurable : Measurable profile)
    (frequency : ℝ) : RandomFunction ℝ where
  Param := AddCircle period
  prior := AddCircle.haarAddCircle  -- the uniform distribution on the circle
  eval phase input := profile (↑(frequency * input) + phase)
  measurable_eval _ := profile_is_measurable.comp (measurable_const_add _)

/-- At every input, the wave's output is distributed as the profile at a
uniform phase. -/
theorem marginal_randomPhaseWave
    (profile_is_measurable : Measurable profile)
    (frequency input : ℝ) :
    let wave :=
      MAKE_RANDOM_PHASE_WAVE profile profile_is_measurable frequency
    let output_distribution := wave.marginal input
    let profile_at_uniform_phase :=
      Measure.map profile AddCircle.haarAddCircle  -- neither the frequency nor the input appears
    output_distribution = profile_at_uniform_phase := by
  unfold_named_pieces
  -- The output is the profile at the angle `frequency * input + phase`.
  -- Adding a fixed angle to a uniform phase gives a uniform phase.
  calc (MAKE_RANDOM_PHASE_WAVE profile profile_is_measurable frequency).marginal
        input
      = Measure.map profile
          (Measure.map (↑(frequency * input) + ·) AddCircle.haarAddCircle) :=
        (Measure.map_map profile_is_measurable (measurable_const_add _)).symm
    _ = Measure.map profile AddCircle.haarAddCircle := by
        rw [map_add_left_eq_self]

/-- **Frequency is invisible in the marginals.** -/
theorem marginal_randomPhaseWave_eq
    (profile_is_measurable : Measurable profile)
    (frequency other_frequency : ℝ) :
    let wave :=
      MAKE_RANDOM_PHASE_WAVE profile profile_is_measurable frequency
    let other_wave :=
      MAKE_RANDOM_PHASE_WAVE profile profile_is_measurable other_frequency
    wave.marginal = other_wave.marginal := by
  unfold_named_pieces
  funext input
  rw [marginal_randomPhaseWave, marginal_randomPhaseWave]

section Sine

open Real

instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- The sine as a function on the circle of circumference `2 * PI`. -/
theorem continuous_circleSin :
    Continuous fun angle : AddCircle (2 * PI) => Angle.sin angle :=
  Angle.continuous_sin

/-- The sine `amplitude * sin(frequency * input + phase)` with a uniformly
random phase: the curve family of `scripts/frequency_isolation.py`.

    phase = uniform(0, 2 * PI)
    sine = lambda input: amplitude * sin(frequency * input + phase)
-/
noncomputable def MAKE_RANDOM_PHASE_SINE
    (amplitude frequency : ℝ) : RandomFunction ℝ :=
  MAKE_RANDOM_PHASE_WAVE
    (fun angle => amplitude * Angle.sin angle)  -- the profile: one turn of a sine, which repeats every 2 * PI
    (continuous_circleSin.measurable.const_mul amplitude)
    frequency

/-- The frequency of a random-phase sine does not change its one-point
marginals. -/
theorem marginal_sineWave_eq
    (amplitude frequency other_frequency : ℝ) :
    let sine       := MAKE_RANDOM_PHASE_SINE amplitude frequency
    let other_sine := MAKE_RANDOM_PHASE_SINE amplitude other_frequency
    sine.marginal = other_sine.marginal :=
  marginal_randomPhaseWave_eq _ frequency other_frequency

/-! ## Names for statements about sines -/

/-- The phase of a random-phase sine: a point on the circle.
Python: a float in `[0, 2 * PI)`, where `2 * PI` wraps round to `0`. -/
abbrev SinePhase (amplitude frequency : ℝ) : Type :=
  (MAKE_RANDOM_PHASE_SINE amplitude frequency).Param

/-- The values a sine of this amplitude sweeps:
`[-|amplitude|, |amplitude|]`. -/
abbrev GET_SINE_BAND (amplitude : ℝ) : Set ℝ :=
  Set.Icc (-|amplitude|) |amplitude|

/-- The value lies in the band a sine of this amplitude sweeps.
Python: `-abs(amplitude) <= value <= abs(amplitude)`. -/
abbrev IS_IN_SINE_BAND (amplitude value : ℝ) : Prop :=
  value ∈ GET_SINE_BAND amplitude

/-- Almost every label lies in the band the sine sweeps: every label,
except for a set of data points that is drawn with probability zero.
Python: `all(IS_IN_SINE_BAND(amplitude, label) for (input, label) in data)`. -/
abbrev ARE_LABELS_ALMOST_SURELY_IN_BAND
    (amplitude : ℝ)
    (data_distribution : DataDistribution) : Prop :=
  ∀ᵐ data_point ∂data_distribution,
    IS_IN_SINE_BAND amplitude (GET_LABEL data_point)

/-- The claim holds for every positive frequency and every phase.
Python: `all(claim(frequency, phase) for frequency in positive_reals
for phase in circle)`. -/
abbrev HOLDS_FOR_EVERY_SINE
    (amplitude : ℝ)
    (claim : (frequency : ℝ) → SinePhase amplitude frequency → Prop) : Prop :=
  ∀ frequency : ℝ, 0 < frequency →
    ∀ phase : SinePhase amplitude frequency, claim frequency phase

end Sine

end SquigglyLine
