/-
The verdict on the learning claim.

If every member of a family has the same one-point marginals, then no member
starts closer than another, for any regression loss and any data. Random-phase
waves of different frequencies are such a family. This is the flat
"vertical error" column of the experiment, as a theorem.
-/
import SquigglyLine.Theorem.Conjecture
import SquigglyLine.Theorem.Marginal
import SquigglyLine.Theorem.RandomPhase

namespace SquigglyLine

open MeasureTheory

variable {ι X : Type*} [Preorder ι] [MeasurableSpace X] {ℓ : ℝ → ℝ}

/-- A family with shared one-point marginals never starts closer in a regression loss. -/
theorem not_startsCloser_of_marginal_eq {M : ModelFamily ι X} (hℓ : Measurable ℓ)
    (h : ∀ i j, (M i).marginal = (M j).marginal) {i j : ι} (hij : i < j)
    (μ : Measure (DataPoint X)) : ¬ STARTS_CLOSER (GET_RESIDUAL_LOSS ℓ) M μ :=
  fun hcloser => (hcloser hij).ne (expected_residualLoss_congr hℓ (h j i) μ)

/-- **Squiggliness does not lower the training loss.** Raising the frequency of a
random-phase wave never lowers its expected regression loss. -/
theorem not_startsCloser_randomPhaseWave {T : ℝ} [Fact (0 < T)] {g : AddCircle T → ℝ}
    (hg : Measurable g) (hℓ : Measurable ℓ) (frequency : ι → ℝ) {i j : ι} (hij : i < j)
    (μ : Measure (DataPoint ℝ)) :
    ¬ STARTS_CLOSER (GET_RESIDUAL_LOSS ℓ) (fun i => MAKE_RANDOM_PHASE_WAVE g hg (frequency i)) μ :=
  not_startsCloser_of_marginal_eq hℓ (fun _ _ => marginal_randomPhaseWave_eq hg _ _) hij μ

/-- The learning claim fails for random-phase waves whose frequency grows with size. -/
theorem not_learningClaim_randomPhaseWave {T : ℝ} [Fact (0 < T)] {g : AddCircle T → ℝ}
    (hg : Measurable g) (hℓ : Measurable ℓ) (frequency : ℕ → ℝ) (μ : Measure (DataPoint ℝ)) :
    ¬ LEARNING_CLAIM_HOLDS ℓ (fun m => MAKE_RANDOM_PHASE_WAVE g hg (frequency m)) μ :=
  not_startsCloser_randomPhaseWave hg hℓ frequency Nat.zero_lt_one μ

/-- The experiment of `scripts/frequency_isolation.py`, as a theorem: for sines of any
amplitude and any frequencies, the learning claim fails for every regression loss on every
data distribution. -/
theorem not_learningClaim_sineWave (A : ℝ) (hℓ : Measurable ℓ) (frequency : ℕ → ℝ)
    (μ : Measure (DataPoint ℝ)) : ¬ LEARNING_CLAIM_HOLDS ℓ (fun m => MAKE_RANDOM_PHASE_SINE A (frequency m)) μ :=
  not_startsCloser_of_marginal_eq hℓ (fun _ _ => marginal_sineWave_eq A _ _) Nat.zero_lt_one μ

end SquigglyLine
