/-
Vocabulary of the squiggly line conjecture.

A network computes a function `f : X → ℝ`. Its graph is the "squiggly line".
A data point is a pair `(x, y)`. Two costs compare the two:

* `nearestDist`  : distance from the data point to the nearest point of the
                   line. This is the loss of the conjecture.
* `residualLoss` : any loss that reads only the residual `y - f x`. This is
                   what regression trains on. `verticalDist` is the case `|·|`.
-/
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Topology.MetricSpace.HausdorffDistance

namespace SquigglyLine

/-- A labelled example: an input and its real label. -/
abbrev DataPoint (X : Type*) := X × ℝ

/-- A cost charged to a function on one data point. -/
abbrev Cost (X : Type*) := (X → ℝ) → DataPoint X → ℝ

/-- A loss that reads only the residual `y - f x`. Every regression loss has this form. -/
def residualLoss {X : Type*} (ℓ : ℝ → ℝ) : Cost X :=
  fun f p => ℓ (p.2 - f p.1)

/-- The vertical distance `|y - f x|` from a data point to the line. -/
abbrev verticalDist {X : Type*} : Cost X :=
  residualLoss abs

/-- The Euclidean space in which the line and the data live. -/
abbrev Ambient (X : Type*) := WithLp 2 (X × ℝ)

/-- A data point, placed in the ambient Euclidean space. -/
abbrev embed {X : Type*} (p : DataPoint X) : Ambient X :=
  WithLp.toLp 2 p

/-- The squiggly line: the graph of `f`. -/
def curve {X : Type*} (f : X → ℝ) : Set (Ambient X) :=
  Set.range fun x => embed (x, f x)

/-- The point of the line directly above or below a data point. -/
theorem footpoint_mem_curve {X : Type*} (f : X → ℝ) (p : DataPoint X) :
    embed (p.1, f p.1) ∈ curve f :=
  ⟨p.1, rfl⟩

section Geometry

variable {X : Type*} [SeminormedAddCommGroup X]

/-- The Euclidean distance from a data point to the nearest point of the line. -/
noncomputable def nearestDist : Cost X :=
  fun f p => Metric.infDist (embed p) (curve f)

/-- Pythagoras, for two data points in the ambient space. -/
theorem dist_embed (p q : DataPoint X) :
    dist (embed p) (embed q) = √(dist p.1 q.1 ^ 2 + dist p.2 q.2 ^ 2) :=
  WithLp.prod_dist_eq_of_L2 _ _

end Geometry

end SquigglyLine
