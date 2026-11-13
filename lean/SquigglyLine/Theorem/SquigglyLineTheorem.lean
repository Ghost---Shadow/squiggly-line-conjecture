/-
The squiggly line theorem, for sines.

One statement that collects what this project proves about the original
picture. Take the sine `amplitude * sin(frequency * x + phase)` with a random
phase, and data whose labels lie in the band the sine sweeps.

1. *Squigglier is closer, at a known rate.* At every data point and every
   phase the distance to the nearest point of the curve lies between
   `vertical_error / sqrt(1 + (amplitude * frequency)^2)` and
   `PI / frequency`.
2. *All the way.* The average distance goes to zero as the frequency grows.
3. *The loss does not see it.* The average loss, for every regression loss,
   is the same at every frequency.
4. *A small shift cashes it in.* Any target with values in the band is fitted
   exactly after moving each input by at most `PI / frequency`.

So the nearness is real and usable, but it is not a lower loss at the start:
it is a short distance to move. The statement is about sines. For neural
networks the corresponding claim is still a conjecture: see
`docs/open-problems.md`.

## How to read this file

The statement is written as a short script. Read it top to bottom:

* the header says what is given (an amplitude, a loss, the data);
* each `let` names one piece, with a comment above it;
* each `claim_N_...` is one of the four claims above;
* the last line says that all four claims hold.

The names are explained in `Vocabulary.lean`. The proof at the bottom is four
calls, one per claim, to lemmas proved in `SineCloser.lean`.

A simpler version, with a plain dataset in place of a distribution, is in
`HighSchool/SquigglyLineTheorem.lean`.

## The same statement in Python

    # Given
    amplitude: float
    loss_fn: Callable[[float], float]         # e.g. lambda r: r ** 2
    data_distribution: Sampler[(x, y)]        # labels inside the band

    # Named pieces
    def sine_curve(frequency, phase):
        return lambda x: amplitude * sin(frequency * x + phase)

    def average_distance(frequency):
        return mean(NEAREST_DIST(sine_curve(frequency, phase), data_point)
                    for data_point in data_distribution
                    for phase in uniform(0, 2 * pi))

    def average_loss(frequency):
        return mean(loss_fn(y - sine_curve(frequency, phase)(x))
                    for (x, y) in data_distribution
                    for phase in uniform(0, 2 * pi))

    # Claim 1, for every frequency > 0, phase and in-band data point
    slope_bound = sqrt(1 + (amplitude * frequency) ** 2)
    lower_bound = vertical_error / slope_bound
    upper_bound = pi / frequency
    assert lower_bound <= nearest_distance <= upper_bound

    # Claim 2
    assert average_distance(frequency) -> 0 as frequency -> infinity

    # Claim 3, for every two frequencies
    assert average_loss(frequency) == average_loss(other_frequency)

    # Claim 4, for every frequency > 0, phase and in-band target
    max_shift = pi / frequency
    warp = ...  # exists
    assert all(abs(x - warp(x)) <= max_shift for x in all_reals)
    assert all(sine_curve(frequency, phase)(warp(x)) == target(x)
               for x in all_reals)
-/
import SquigglyLine.Theorem.SineCloser
import SquigglyLine.Theorem.Vocabulary

namespace SquigglyLine

open MeasureTheory Real

/-- **The squiggly line theorem (for sines).** A squigglier curve is closer
to the data, at rate `1 / frequency` and all the way to zero. No regression
loss sees this at the start, and a shift of the input no larger than that
distance turns it into an exact fit. -/
theorem squiggly_line_theorem
    -- Given: the height of the sine.
    (amplitude : ℝ)
    -- Given: a loss on the residual, such as `r ^ 2` or `|r|`.
    {loss_fn : RealFunction}
    (loss_is_measurable : Measurable loss_fn)
    -- Given: the data, as a distribution over `(x, y)` pairs.
    {data_distribution : DataDistribution}
    [IsProbabilityMeasure data_distribution]
    -- Given: the labels lie in the band the sine sweeps.
    (labels_in_band :
      LabelsAlmostSurelyInBand amplitude data_distribution) :

    -- The curve drawn by one frequency and one phase.
    let sine_curve :=
      fun (frequency : ℝ) (phase : SinePhase amplitude frequency) =>
        (SINE_WAVE amplitude frequency).eval phase

    -- The nearest distance, averaged over the data and the random phase.
    let average_distance :=
      fun (frequency : ℝ) =>
        (SINE_WAVE amplitude frequency).expected
          NEAREST_DIST data_distribution

    -- The loss, averaged over the data and the random phase.
    let average_loss :=
      fun (frequency : ℝ) =>
        (SINE_WAVE amplitude frequency).expected
          (RESIDUAL_LOSS loss_fn) data_distribution

    -- Claim 1: the distance is squeezed between two bounds.
    let claim_1_distance_is_squeezed : Prop :=
      ForEverySine amplitude fun frequency phase =>
        ∀ data_point : DataPoint ℝ,
          let curve            := sine_curve frequency phase
          let vertical_error   := VERTICAL_DIST curve data_point
          let nearest_distance := NEAREST_DIST curve data_point
          let slope_bound      := √(1 + (amplitude * frequency) ^ 2)
          let lower_bound      := vertical_error / slope_bound
          let upper_bound      := PI / frequency
          let label_is_in_band :=
            LABEL_OF data_point ∈ SineBand amplitude
          let is_above_lower_bound := lower_bound ≤ nearest_distance
          let is_below_upper_bound := nearest_distance ≤ upper_bound
          label_is_in_band →
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

  -- Proof of claim 1: the two bounds, proved point by point for sines.
  have proof_of_claim_1 : claim_1_distance_is_squeezed := by
    intro frequency frequency_pos phase data_point
    exact sineWave_nearestDist_bounds amplitude frequency_pos phase
      data_point

  -- Proof of claims 2 and 3: one lemma gives both, as a pair.
  have closer_and_no_better :=
    closer_but_no_better amplitude loss_is_measurable labels_in_band
  have proof_of_claim_2 : claim_2_distance_vanishes :=
    closer_and_no_better.1
  have proof_of_claim_3 : claim_3_loss_is_flat :=
    closer_and_no_better.2

  -- Proof of claim 4: a sine that covers its band can be warped to fit.
  have proof_of_claim_4 : claim_4_warp_fits_any_target := by
    intro frequency frequency_pos phase target
    exact sineWave_exists_warp amplitude frequency_pos phase target

  -- All four together.
  exact ⟨proof_of_claim_1, proof_of_claim_2,
    proof_of_claim_3, proof_of_claim_4⟩

end SquigglyLine
