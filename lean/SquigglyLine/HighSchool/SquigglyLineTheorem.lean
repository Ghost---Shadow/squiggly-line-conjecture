/-
The squiggly line theorem for sines: the high-school version.

This is a reduced version of `Theorem/SquigglyLineTheorem.lean`, written so
that it can be followed with high-school mathematics. It makes the same four
claims. Two things are made simpler:

| The full theorem                         | This version                      |
|------------------------------------------|-----------------------------------|
| the data is a probability distribution   | the data is a list of `n` points  |
| the loss is any measurable function      | the loss is any continuous one    |

So "average over the data" is a plain sum divided by `n`, and "almost every
label" is "every label". A continuous loss covers squared error, absolute
error and Huber. It leaves out losses with a jump, such as the 0-1 loss; the
full theorem covers those too.

One thing cannot be made simpler. The phase of the sine is drawn uniformly
from a circle, so the average over the phase is an integral, written
`∫ phase, ... ∂(prior)`. Read it as "the mean over every phase from `0` to
`2 * PI`". A finite grid of phases would not do: shifting a grid by an
amount that is not on the grid does not give back the same grid, and claim 3
would be false.

Every statement proved here follows from the full theorem's lemmas. Nothing
here is used by the full theorem.

## The proof in plain words

* **Claim 1** is the two-sided bound for one data point
  (`sineWave_nearestDist_bounds`), used on each point of the dataset.
* **Claim 2** is a squeeze. A sine takes every value of its band within half
  a period of any input, so each distance is at most `PI / frequency`. The
  mean over the phase is then at most `PI / frequency` (step A), and so is
  the mean over the `n` points (step B). The mean is never below zero, and
  `PI / frequency` goes to zero.
* **Claim 3**. At one fixed input, the output of a random-phase sine has the
  same distribution at every frequency: changing the frequency only shifts
  the phase, and a uniformly random phase stays uniform after a shift. The
  mean loss at that point depends only on that distribution. So the `n`
  terms of the sum agree one by one.
* **Claim 4** is the warp lemma (`sineWave_exists_warp`).

## The same statement in Python

    # Given
    amplitude: float
    loss_fn: Callable[[float], float]         # continuous
    dataset: list[tuple[float, float]]        # n >= 1 points, labels in band

    # Named pieces
    def sine_curve(frequency, phase):
        return lambda x: amplitude * sin(frequency * x + phase)

    def SINE_CURVE_AVERAGE(cost, frequency):
        return (1 / n) * sum(
            mean(cost(sine_curve(frequency, phase), data_point)
                 for phase in uniform(0, 2 * PI))
            for data_point in dataset)

    def average_distance(frequency):
        return SINE_CURVE_AVERAGE(NEAREST_DIST, frequency)

    def average_loss(frequency):
        return SINE_CURVE_AVERAGE(RESIDUAL_LOSS(loss_fn), frequency)

    # Claims 1 to 4: as in the full theorem, with "for every data point"
    # read as "for every index i in range(n)".
-/
import SquigglyLine.Theorem.SineCloser
import SquigglyLine.Theorem.Vocabulary

namespace SquigglyLine.HighSchool

open MeasureTheory Filter Topology Real

/-- The mean of a cost over the dataset and over the random phase of the
sine.
Python: `(1 / n) * sum(mean_over_phase(cost, data_point) for data_point in
dataset)`. -/
noncomputable def SINE_CURVE_AVERAGE (cost : Cost ℝ)
    (amplitude frequency : ℝ) {n : ℕ} (dataset : Dataset n) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : DataIndex n,
    ∫ phase, cost ((SINE_WAVE amplitude frequency).eval phase) (dataset i)
      ∂(SINE_WAVE amplitude frequency).prior

/-- **The squiggly line theorem for sines, on a finite dataset.** A
squigglier sine is closer to every data point, at rate `1 / frequency` and
all the way to zero. No continuous regression loss sees this, and a shift of
the input no larger than that distance turns it into an exact fit. -/
theorem squiggly_line_theorem_finite
    -- Given: the height of the sine.
    (amplitude : ℝ)
    -- Given: a continuous loss on the residual, such as `r ^ 2` or `|r|`.
    {loss_fn : RealFunction}
    (loss_is_continuous : Continuous loss_fn)
    -- Given: a dataset of at least one point.
    {n : ℕ}
    (n_pos : 0 < n)
    (dataset : Dataset n)
    -- Given: every label lies in the band the sine sweeps.
    (labels_in_band : LabelsInBand amplitude dataset) :

    -- The curve drawn by one frequency and one phase.
    let sine_curve :=
      fun (frequency : ℝ) (phase : SinePhase amplitude frequency) =>
        (SINE_WAVE amplitude frequency).eval phase

    -- The nearest distance, averaged over the dataset and the phase.
    let average_distance :=
      fun (frequency : ℝ) =>
        SINE_CURVE_AVERAGE NEAREST_DIST amplitude frequency dataset

    -- The loss, averaged over the dataset and the phase.
    let average_loss :=
      fun (frequency : ℝ) =>
        SINE_CURVE_AVERAGE (RESIDUAL_LOSS loss_fn)
          amplitude frequency dataset

    -- Claim 1: the distance is squeezed between two bounds.
    let claim_1_distance_is_squeezed : Prop :=
      ForEverySine amplitude fun frequency phase =>
        ∀ i : DataIndex n,
          let curve            := sine_curve frequency phase
          let data_point       := dataset i
          let vertical_error   := VERTICAL_DIST curve data_point
          let nearest_distance := NEAREST_DIST curve data_point
          let slope_bound      := √(1 + (amplitude * frequency) ^ 2)
          let lower_bound      := vertical_error / slope_bound
          let upper_bound      := PI / frequency
          let is_above_lower_bound := lower_bound ≤ nearest_distance
          let is_below_upper_bound := nearest_distance ≤ upper_bound
          is_above_lower_bound ∧ is_below_upper_bound

    -- Claim 2: the average distance goes to zero.
    let claim_2_distance_vanishes : Prop :=
      GoesToZeroAsInputGrows average_distance

    -- Claim 3: the average loss is the same at every frequency.
    let claim_3_loss_is_flat : Prop :=
      ∀ frequency other_frequency : ℝ,
        average_loss frequency = average_loss other_frequency

    -- Claim 4: a small shift of the input fits any target in the band.
    let claim_4_warp_fits_any_target : Prop :=
      ForEverySine amplitude fun frequency phase =>
        ∀ target : RealFunction,
          let max_shift := PI / frequency
          let target_stays_in_band :=
            ∀ input, target input ∈ SineBand amplitude
          target_stays_in_band → ∃ warp : Warp,
            let moves_each_input_a_little :=
              ∀ input, dist input (warp input) ≤ max_shift
            let hits_the_target :=
              ∀ input,
                sine_curve frequency phase (warp input) = target input
            moves_each_input_a_little ∧ hits_the_target

    -- The theorem: all four claims hold.
    claim_1_distance_is_squeezed ∧
    claim_2_distance_vanishes ∧
    claim_3_loss_is_flat ∧
    claim_4_warp_fits_any_target := by

  -- Bring the named pieces and the four claims into scope.
  intro sine_curve average_distance average_loss
    claim_1_distance_is_squeezed claim_2_distance_vanishes
    claim_3_loss_is_flat claim_4_warp_fits_any_target

  -- The loss is continuous, and that is enough to take its average.
  have loss_is_measurable : Measurable loss_fn :=
    loss_is_continuous.measurable

  -- The dataset is not empty, so dividing by `n` is safe.
  have n_is_not_zero : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr n_pos.ne'

  -- Step A: for one data point, the distance averaged over the phase is at
  -- most `PI / frequency`, because it is at most that at every phase.
  have phase_average_is_small :
      ∀ frequency : ℝ, 0 < frequency → ∀ i : DataIndex n,
        ∫ phase,
            NEAREST_DIST ((SINE_WAVE amplitude frequency).eval phase)
              (dataset i)
          ∂(SINE_WAVE amplitude frequency).prior
        ≤ PI / frequency := by
    intro frequency frequency_pos i
    have distance_is_never_negative :
        ∀ phase : SinePhase amplitude frequency,
          0 ≤ NEAREST_DIST ((SINE_WAVE amplitude frequency).eval phase)
            (dataset i) :=
      fun phase => nearestDist_nonneg _ _
    have distance_is_small_at_every_phase :
        ∀ phase : SinePhase amplitude frequency,
          NEAREST_DIST ((SINE_WAVE amplitude frequency).eval phase)
            (dataset i) ≤ PI / frequency :=
      fun phase =>
        nearestDist_le_of_coversWithin
          (sineWave_coversWithin amplitude frequency_pos phase)
          (dataset i) (labels_in_band i)
    calc ∫ phase,
            NEAREST_DIST ((SINE_WAVE amplitude frequency).eval phase)
              (dataset i)
          ∂(SINE_WAVE amplitude frequency).prior
        ≤ ∫ _phase, PI / frequency
            ∂(SINE_WAVE amplitude frequency).prior :=
          integral_mono_of_nonneg
            (ae_of_all _ distance_is_never_negative)
            (integrable_const _)
            (ae_of_all _ distance_is_small_at_every_phase)
      _ = PI / frequency := by simp

  -- Step B: so the average over the `n` data points is at most
  -- `PI / frequency` too.
  have average_distance_is_small :
      ∀ frequency : ℝ, 0 < frequency →
        average_distance frequency ≤ PI / frequency := by
    intro frequency frequency_pos
    have sum_is_small :
        ∑ i : DataIndex n,
            ∫ phase,
                NEAREST_DIST ((SINE_WAVE amplitude frequency).eval phase)
                  (dataset i)
              ∂(SINE_WAVE amplitude frequency).prior
          ≤ ∑ _i : DataIndex n, PI / frequency :=
      Finset.sum_le_sum fun i _ =>
        phase_average_is_small frequency frequency_pos i
    calc average_distance frequency
        ≤ (1 / (n : ℝ)) * ∑ _i : DataIndex n, PI / frequency :=
          mul_le_mul_of_nonneg_left sum_is_small (by positivity)
      _ = PI / frequency := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          field_simp

  -- Step C: the average distance is never negative.
  have average_distance_is_never_negative :
      ∀ frequency : ℝ, 0 ≤ average_distance frequency := by
    intro frequency
    have each_term_is_never_negative :
        ∀ i : DataIndex n,
          0 ≤ ∫ phase,
              NEAREST_DIST ((SINE_WAVE amplitude frequency).eval phase)
                (dataset i)
            ∂(SINE_WAVE amplitude frequency).prior :=
      fun i => integral_nonneg fun phase => nearestDist_nonneg _ _
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun i _ => each_term_is_never_negative i)

  -- Proof of claim 1: the two bounds, used on each point of the dataset.
  have proof_of_claim_1 : claim_1_distance_is_squeezed := by
    intro frequency frequency_pos phase i
    exact sineWave_nearestDist_bounds amplitude frequency_pos phase
      (dataset i) (labels_in_band i)

  -- Proof of claim 2: squeezed between zero and `PI / frequency`, and
  -- `PI / frequency` goes to zero.
  have proof_of_claim_2 : claim_2_distance_vanishes := by
    have upper_bound_goes_to_zero :
        GoesToZeroAsInputGrows fun frequency => PI / frequency :=
      tendsto_const_nhds.div_atTop tendsto_id
    have is_small_for_positive_frequencies :
        ∀ᶠ frequency in atTop,
          average_distance frequency ≤ PI / frequency :=
      (eventually_gt_atTop 0).mono average_distance_is_small
    exact squeeze_zero'
      (Eventually.of_forall average_distance_is_never_negative)
      is_small_for_positive_frequencies
      upper_bound_goes_to_zero

  -- Proof of claim 3: at each data point the output of the sine has the
  -- same distribution at both frequencies, so the two sums agree term by
  -- term.
  have proof_of_claim_3 : claim_3_loss_is_flat := by
    intro frequency other_frequency
    have same_output_distribution :
        (SINE_WAVE amplitude frequency).marginal
          = (SINE_WAVE amplitude other_frequency).marginal :=
      marginal_sineWave_eq amplitude frequency other_frequency
    have each_term_is_equal :
        ∀ i : DataIndex n,
          ∫ phase,
              RESIDUAL_LOSS loss_fn
                ((SINE_WAVE amplitude frequency).eval phase) (dataset i)
            ∂(SINE_WAVE amplitude frequency).prior
          = ∫ phase,
              RESIDUAL_LOSS loss_fn
                ((SINE_WAVE amplitude other_frequency).eval phase)
                (dataset i)
            ∂(SINE_WAVE amplitude other_frequency).prior := by
      intro i
      rw [integral_residualLoss_eq_integral_marginal _ loss_is_measurable,
        integral_residualLoss_eq_integral_marginal _ loss_is_measurable,
        same_output_distribution]
    show SINE_CURVE_AVERAGE _ _ _ _ = SINE_CURVE_AVERAGE _ _ _ _
    unfold SINE_CURVE_AVERAGE
    rw [Finset.sum_congr rfl fun i _ => each_term_is_equal i]

  -- Proof of claim 4: a sine that covers its band can be warped to fit.
  have proof_of_claim_4 : claim_4_warp_fits_any_target := by
    intro frequency frequency_pos phase target
    exact sineWave_exists_warp amplitude frequency_pos phase target

  -- All four together.
  exact ⟨proof_of_claim_1, proof_of_claim_2,
    proof_of_claim_3, proof_of_claim_4⟩

end SquigglyLine.HighSchool
