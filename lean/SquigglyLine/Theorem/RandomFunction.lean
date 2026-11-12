/-
A randomly initialised model.

`RandomFunction X` is a parameter space, an initialisation distribution on it,
and the function that each parameter value computes. Networks of different
sizes have different parameter spaces, so the parameter space is a field and
not an argument.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import SquigglyLine.Theorem.Defs

namespace SquigglyLine

open MeasureTheory

/-- A function `X → ℝ` whose parameters are drawn at random. -/
structure RandomFunction (X : Type*) where
  /-- The parameter space. -/
  Param : Type
  [measurableSpace : MeasurableSpace Param]
  /-- The initialisation distribution. -/
  prior : Measure Param
  [isProbabilityMeasure : IsProbabilityMeasure prior]
  /-- The function computed with the given parameters. -/
  eval : Param → X → ℝ
  /-- At each fixed input, the output is a random variable. -/
  measurable_eval : ∀ x, Measurable fun θ => eval θ x

namespace RandomFunction

attribute [instance] measurableSpace isProbabilityMeasure

variable {X : Type*} (F : RandomFunction X)

/-- The one-point marginal: the distribution of the output at a single input. -/
noncomputable def marginal (x : X) : Measure ℝ :=
  F.prior.map fun θ => F.eval θ x

/-- The expected cost at initialisation, on data drawn from `μ`. -/
noncomputable def expected [MeasurableSpace X] (cost : Cost X) (μ : Measure (DataPoint X)) : ℝ :=
  ∫ p, ∫ θ, cost (F.eval θ) p ∂F.prior ∂μ

end RandomFunction

end SquigglyLine
