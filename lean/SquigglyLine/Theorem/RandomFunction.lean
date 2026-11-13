/-
A randomly initialised model.

`RandomFunction Inputs` is a parameter space, an initialisation distribution
on it, and the model that each parameter value computes. Networks of
different sizes have different parameter spaces, so the parameter space is a
field and not an argument.

| Name                     | Meaning                                         |
|--------------------------|-------------------------------------------------|
| `RandomFunction Inputs`  | a model whose parameters are drawn at random    |
| `.Param`                 | the type of its parameters                      |
| `.prior`                 | how the parameters are drawn                    |
| `.eval parameters`       | the model computed with those parameters        |
| `.marginal input`        | the distribution of the output at one input     |
| `.expected cost data`    | the cost, averaged over the data and the draw   |
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import SquigglyLine.Theorem.Vocabulary

namespace SquigglyLine

open MeasureTheory

/-- A model `Inputs → ℝ` whose parameters are drawn at random.

    class RandomFunction:
        Param: type                              # the parameter space
        prior: Sampler[Param]                    # how parameters are drawn
        def eval(parameters) -> Model: ...       # the model they compute
-/
structure RandomFunction (Inputs : Type*) where
  /-- The parameter space. -/
  Param : Type
  [measurableSpace : MeasurableSpace Param]
  /-- The initialisation distribution. -/
  prior : Measure Param
  [isProbabilityMeasure : IsProbabilityMeasure prior]
  /-- The model computed with the given parameters. -/
  eval : Param → Model Inputs
  /-- At each fixed input, the output is a random variable. -/
  measurable_eval : ∀ input, Measurable fun parameters => eval parameters input

namespace RandomFunction

attribute [instance] measurableSpace isProbabilityMeasure

variable {Inputs : Type*} (random_model : RandomFunction Inputs)

/-- The one-point marginal: the distribution of the output at a single
input.
Python: `[random_model.eval(parameters)(input) for parameters in prior]`,
as a distribution. -/
noncomputable def marginal (input : Inputs) : Measure ℝ :=
  let output_at_input := fun parameters => random_model.eval parameters input
  random_model.prior.map output_at_input

/-- The expected cost at initialisation, on data drawn from
`data_distribution`.
Python: `mean(cost(random_model.eval(parameters), data_point)
for data_point in data_distribution for parameters in prior)`. -/
noncomputable def expected [MeasurableSpace Inputs]
    (cost : Cost Inputs)
    (data_distribution : DataDistributionOver Inputs) : ℝ :=
  ∫ data_point,
    ∫ parameters, cost (random_model.eval parameters) data_point
      ∂random_model.prior
    ∂data_distribution

end RandomFunction

end SquigglyLine
