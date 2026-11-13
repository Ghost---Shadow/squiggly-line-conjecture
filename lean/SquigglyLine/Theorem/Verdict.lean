/-
The verdict on the learning claim.

If every member of a family has the same one-point marginals, then no member
starts closer than another, for any regression loss and any data.
Random-phase waves of different frequencies are such a family. This is the
flat "vertical error" column of the experiment, as a theorem.

Theorems:

* `not_startsCloser_of_marginal_eq`    shared marginals: nobody starts closer;
* `not_startsCloser_randomPhaseWave`   so not for random-phase waves;
* `not_learningClaim_randomPhaseWave`  so the learning claim fails for them;
* `not_learningClaim_sineWave`         and for sines in particular.
-/
import SquigglyLine.Theorem.Conjecture
import SquigglyLine.Theorem.Marginal
import SquigglyLine.Theorem.RandomPhase

namespace SquigglyLine

open MeasureTheory

variable {Size Inputs : Type*} [Preorder Size] [MeasurableSpace Inputs]
  {loss_fn : RealFunction}

/-- A family with shared one-point marginals never starts closer in a
regression loss. -/
theorem not_startsCloser_of_marginal_eq
    {model_family : ModelFamily Size Inputs}
    (loss_is_measurable : Measurable loss_fn)
    (all_marginals_agree :
      ∀ size other_size,
        (model_family size).marginal = (model_family other_size).marginal)
    {smaller bigger : Size}
    (smaller_lt_bigger : smaller < bigger)  -- the family has two different sizes to compare
    (data_distribution : DataDistributionOver Inputs) :
    let bigger_starts_closer :=
      STARTS_CLOSER (GET_RESIDUAL_LOSS loss_fn) model_family data_distribution
    ¬ bigger_starts_closer :=
  -- "Starts closer" would make the two expected losses different, and
  -- equal marginals make them equal.
  fun starts_closer =>
    (starts_closer smaller_lt_bigger).ne
      (expected_residualLoss_congr loss_is_measurable
        (all_marginals_agree bigger smaller) data_distribution)

/-- **Squiggliness does not lower the training loss.** Raising the frequency
of a random-phase wave never lowers its expected regression loss. -/
theorem not_startsCloser_randomPhaseWave
    {period : ℝ} [Fact (0 < period)]
    {profile : Profile period}
    (profile_is_measurable : Measurable profile)
    (loss_is_measurable : Measurable loss_fn)
    (frequency_of : Size → ℝ)
    {smaller bigger : Size}
    (smaller_lt_bigger : smaller < bigger)
    (data_distribution : DataDistribution) :
    let wave_family := fun size =>
      MAKE_RANDOM_PHASE_WAVE profile profile_is_measurable (frequency_of size)
    let bigger_starts_closer :=
      STARTS_CLOSER (GET_RESIDUAL_LOSS loss_fn) wave_family data_distribution
    ¬ bigger_starts_closer :=
  not_startsCloser_of_marginal_eq loss_is_measurable
    (fun _ _ => marginal_randomPhaseWave_eq profile_is_measurable _ _)
    smaller_lt_bigger data_distribution

/-- The learning claim fails for random-phase waves whose frequency grows
with size. -/
theorem not_learningClaim_randomPhaseWave
    {period : ℝ} [Fact (0 < period)]
    {profile : Profile period}
    (profile_is_measurable : Measurable profile)
    (loss_is_measurable : Measurable loss_fn)
    (frequency_of : ℕ → ℝ)
    (data_distribution : DataDistribution) :
    let wave_family := fun size =>
      MAKE_RANDOM_PHASE_WAVE profile profile_is_measurable (frequency_of size)
    let learning_claim :=
      LEARNING_CLAIM_HOLDS loss_fn wave_family data_distribution
    ¬ learning_claim :=
  not_startsCloser_randomPhaseWave profile_is_measurable loss_is_measurable
    frequency_of Nat.zero_lt_one data_distribution  -- sizes 0 and 1 are enough to compare

/-- The experiment of `scripts/frequency_isolation.py`, as a theorem: for
sines of any amplitude and any frequencies, the learning claim fails for
every regression loss on every data distribution. -/
theorem not_learningClaim_sineWave
    (amplitude : ℝ)
    (loss_is_measurable : Measurable loss_fn)
    (frequency_of : ℕ → ℝ)
    (data_distribution : DataDistribution) :
    let sine_family := fun size =>
      MAKE_RANDOM_PHASE_SINE amplitude (frequency_of size)
    let learning_claim :=
      LEARNING_CLAIM_HOLDS loss_fn sine_family data_distribution
    ¬ learning_claim :=
  not_startsCloser_of_marginal_eq loss_is_measurable
    (fun _ _ => marginal_sineWave_eq amplitude _ _)
    Nat.zero_lt_one data_distribution  -- sizes 0 and 1 are enough to compare

end SquigglyLine
