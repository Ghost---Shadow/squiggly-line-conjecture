/-
The conjecture, as statements.

The original idea is two claims of the same shape: "a bigger model starts
closer to the data". They differ only in the cost that defines "closer", so
both are instances of `STARTS_CLOSER`.

| Name                             | Meaning                                |
|----------------------------------|----------------------------------------|
| `ModelFamily Size Inputs`        | one random model for each size         |
| `STARTS_CLOSER`                  | a bigger model has a smaller cost      |
| `SQUIGGLY_LINE_CONJECTURE_HOLDS` | ... in distance to the nearest point   |
| `LEARNING_CLAIM_HOLDS`           | ... in training loss                   |

Nothing here is proved. `Verdict.lean` settles the second claim.
-/
import SquigglyLine.Theorem.RandomFunction

namespace SquigglyLine

open MeasureTheory

variable {Size Inputs : Type*} [Preorder Size] [MeasurableSpace Inputs]

/-- Random models indexed by a size: parameter count, depth, frequency.
Python: `Callable[[Size], RandomFunction]`. -/
abbrev ModelFamily (Size Inputs : Type*) := Size → RandomFunction Inputs

/-- A bigger model has a strictly smaller expected cost at initialisation.
Python: `all(expected_cost(bigger) < expected_cost(smaller)
for smaller, bigger in pairs if smaller < bigger)`. -/
def STARTS_CLOSER
    (cost : Cost Inputs)
    (model_family : ModelFamily Size Inputs)
    (data_distribution : DataDistributionOver Inputs) : Prop :=
  let expected_cost := fun size =>
    (model_family size).expected cost data_distribution
  StrictAnti expected_cost  -- "strictly anti-monotone": goes down whenever the size goes up

/-- **The squiggly line conjecture**: more parameters, smaller expected
distance from the data to the nearest point of the line. -/
def SQUIGGLY_LINE_CONJECTURE_HOLDS [SeminormedAddCommGroup Inputs]
    (model_family : ModelFamily ℕ Inputs)
    (data_distribution : DataDistributionOver Inputs) : Prop :=
  STARTS_CLOSER GET_NEAREST_DISTANCE model_family data_distribution

/-- **The learning claim**: more parameters, smaller expected training loss
before training. -/
def LEARNING_CLAIM_HOLDS
    (loss_fn : RealFunction)
    (model_family : ModelFamily ℕ Inputs)
    (data_distribution : DataDistributionOver Inputs) : Prop :=
  STARTS_CLOSER (GET_RESIDUAL_LOSS loss_fn) model_family data_distribution

end SquigglyLine
