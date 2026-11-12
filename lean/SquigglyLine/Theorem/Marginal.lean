/-
A regression loss sees only one-point marginals.

The expected loss of a random function at initialisation depends on the
distribution of its output at each single input, and on nothing else. How the
outputs at two different inputs move together (which is what "squiggly" means)
does not enter.
-/
import SquigglyLine.Theorem.RandomFunction

namespace SquigglyLine

open MeasureTheory

variable {X : Type*} {F G : RandomFunction X} {ℓ : ℝ → ℝ}

/-- The expected loss on one data point is an integral against the one-point marginal. -/
theorem integral_residualLoss_eq_integral_marginal (F : RandomFunction X) (hℓ : Measurable ℓ)
    (p : DataPoint X) :
    ∫ θ, residualLoss ℓ (F.eval θ) p ∂F.prior = ∫ t, ℓ (p.2 - t) ∂F.marginal p.1 :=
  (integral_map (F.measurable_eval p.1).aemeasurable
    (hℓ.comp (measurable_const.sub measurable_id)).aestronglyMeasurable).symm

/-- **Marginal lemma.** Equal one-point marginals give equal expected loss, on any data. -/
theorem expected_residualLoss_congr [MeasurableSpace X] (hℓ : Measurable ℓ)
    (h : F.marginal = G.marginal) (μ : Measure (DataPoint X)) :
    F.expected (residualLoss ℓ) μ = G.expected (residualLoss ℓ) μ := by
  simp only [RandomFunction.expected, integral_residualLoss_eq_integral_marginal _ hℓ, h]

end SquigglyLine
