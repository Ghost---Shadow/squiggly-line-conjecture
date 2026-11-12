/-
The squiggly line theorem, for sines.

One statement that collects what this project proves about the original
picture. Take the random-phase sine `A * sin (w * x + φ)` and data whose labels
lie in the band the sine sweeps.

1. *Squigglier is closer, at a known rate.* At every data point and every
   phase the distance to the nearest point of the curve lies between the
   vertical error divided by `√(1 + (A w)²)` and `π / w`.
2. *All the way.* The expected distance tends to zero as the frequency grows.
3. *The loss does not see it.* The expected loss, for every regression loss,
   is the same at every frequency.
4. *A small shift cashes it in.* Any target with values in the band is fitted
   exactly after moving each input by at most `π / w`.

So the nearness is real and usable, but it is not a lower loss at the start:
it is a short distance to move. The statement is about sines. For neural
networks the corresponding claim is still a conjecture: see
`docs/open-problems.md`.
-/
import SquigglyLine.Theorem.SineCloser

namespace SquigglyLine

open MeasureTheory Filter Topology Real

/-- **The squiggly line theorem (for sines).** A squigglier curve is closer to the data, at
rate `1 / frequency` and all the way to zero. No regression loss sees this at the start, and
a shift of the input no larger than that distance turns it into an exact fit. -/
theorem squiggly_line_theorem (A : ℝ) {ℓ : ℝ → ℝ} (hℓ : Measurable ℓ)
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
  ⟨fun hw φ p hp => sineWave_nearestDist_bounds A hw φ p hp,
    (closer_but_no_better A hℓ hμ).1, (closer_but_no_better A hℓ hμ).2,
    fun hw φ target ht => sineWave_exists_warp A hw φ target ht⟩

end SquigglyLine
