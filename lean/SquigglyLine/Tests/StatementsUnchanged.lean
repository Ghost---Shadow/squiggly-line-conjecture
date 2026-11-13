/-
Tests: a restyled statement says what the original statement said.

Restyling a theorem changes its names and its layout. It must not change the
mathematics. This file is the check.

Each test below writes a statement out in the original notation, with
Mathlib's short names and nothing folded away, and proves it in one step from
the restyled theorem. Lean accepts that step only if the two statements
unfold to the same thing. So if a restyle ever changes what a theorem says,
this file stops building and CI fails.

This is the one place where single letters and Greek are kept on purpose:
the left-hand side of each check has to be the original text.

| Test                             | Checks                                    |
|----------------------------------|-------------------------------------------|
| `squiggly_line_theorem` example  | `Theorem/SquigglyLineTheorem.lean`        |
-/
import SquigglyLine.Theorem.SquigglyLineTheorem

namespace SquigglyLine.Tests

open MeasureTheory Filter Topology Real

/-- `squiggly_line_theorem`, as it was stated before the restyle. -/
example (A : ℝ) {ℓ : ℝ → ℝ} (hℓ : Measurable ℓ)
    {μ : Measure (DataPoint ℝ)} [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ p ∂μ, p.2 ∈ Set.Icc (-|A|) |A|) :
    (∀ {w : ℝ}, 0 < w → ∀ (φ : (sineWave A w).Param) (p : DataPoint ℝ),
        p.2 ∈ Set.Icc (-|A|) |A| →
          verticalDist ((sineWave A w).eval φ) p / √(1 + (A * w) ^ 2)
              ≤ nearestDist ((sineWave A w).eval φ) p ∧
            nearestDist ((sineWave A w).eval φ) p ≤ π / w) ∧
      Tendsto (fun w : ℝ => (sineWave A w).expected nearestDist μ) atTop (𝓝 0) ∧
      (∀ w w' : ℝ, (sineWave A w).expected (residualLoss ℓ) μ
        = (sineWave A w').expected (residualLoss ℓ) μ) ∧
      ∀ {w : ℝ}, 0 < w → ∀ (φ : (sineWave A w).Param) (target : ℝ → ℝ),
        (∀ x, target x ∈ Set.Icc (-|A|) |A|) →
          ∃ warp : ℝ → ℝ, (∀ x, dist x (warp x) ≤ π / w) ∧
            ∀ x, (sineWave A w).eval φ (warp x) = target x :=
  squiggly_line_theorem A hℓ hμ

end SquigglyLine.Tests
