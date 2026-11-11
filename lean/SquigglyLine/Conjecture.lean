/-
The conjecture, as statements.

The 2022 idea is two claims of the same shape: "a bigger model starts closer
to the data". They differ only in the cost that defines "closer", so both are
instances of `StartsCloser`.

Nothing here is proved. `Verdict.lean` settles the second claim.
-/
import SquigglyLine.RandomFunction

namespace SquigglyLine

open MeasureTheory

variable {ι X : Type*} [Preorder ι] [MeasurableSpace X]

/-- Random functions indexed by a size: parameter count, depth, frequency. -/
abbrev ModelFamily (ι X : Type*) := ι → RandomFunction X

/-- A bigger model has a strictly smaller expected cost at initialisation. -/
def StartsCloser (cost : Cost X) (M : ModelFamily ι X) (μ : Measure (DataPoint X)) : Prop :=
  StrictAnti fun i => (M i).expected cost μ

/-- **The squiggly line conjecture**: more parameters, smaller
expected distance from the data to the nearest point of the line. -/
def SquigglyLineConjecture [SeminormedAddCommGroup X] (M : ModelFamily ℕ X)
    (μ : Measure (DataPoint X)) : Prop :=
  StartsCloser nearestDist M μ

/-- **The learning claim**: more parameters, smaller expected training loss before training. -/
def LearningClaim (ℓ : ℝ → ℝ) (M : ModelFamily ℕ X) (μ : Measure (DataPoint X)) : Prop :=
  StartsCloser (residualLoss ℓ) M μ

end SquigglyLine
