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

The file is written as a short script. Read it top to bottom:

* three helper functions come first, each with its Python reading;
* the theorem's header says what is given (an amplitude, a loss, the data);
* each `let` names one piece;
* a comment at the end of a line says why that line is what it is. Lines
  that explain themselves have none;
* each `claim_N_...` is one of the four claims above;
* the last line says that all four claims hold.

The names are explained in `Vocabulary.lean`. The proof at the bottom is four
calls, one per claim, to lemmas proved in `SineCloser.lean`.

## The same statement in Python

    # Given
    amplitude: float
    loss_fn: Callable[[float], float]         # e.g. lambda r: r ** 2
    data_distribution: Sampler[(x, y)]        # labels inside the band

    # Claim 1, for every frequency > 0, phase and data point
    curve = DRAW_SINE_CURVE(amplitude, frequency, phase)
    vertical_error = GET_VERTICAL_ERROR(curve, data_point)
    nearest_distance = GET_NEAREST_DISTANCE(curve, data_point)
    slope_bound = sqrt(1 + (amplitude * frequency) ** 2)
    lower_bound = vertical_error / slope_bound
    upper_bound = PI / frequency
    if IS_IN_SINE_BAND(amplitude, GET_LABEL(data_point)):
        assert lower_bound <= nearest_distance <= upper_bound

    # Claim 2
    assert GET_AVERAGE_DISTANCE(amplitude, data_distribution, frequency) \
        -> 0 as frequency -> infinity

    # Claim 3, for every two frequencies
    loss_here = GET_AVERAGE_LOSS(
        amplitude, loss_fn, data_distribution, frequency)
    loss_there = GET_AVERAGE_LOSS(
        amplitude, loss_fn, data_distribution, other_frequency)
    assert loss_here == loss_there

    # Claim 4, for every frequency > 0, phase and target in the band
    curve = DRAW_SINE_CURVE(amplitude, frequency, phase)
    max_shift = PI / frequency
    warp = ...  # exists
    assert all(abs(x - warp(x)) <= max_shift for x in all_reals)
    assert all(curve(warp(x)) == target(x) for x in all_reals)
-/
import SquigglyLine.Theorem.SineCloser
import SquigglyLine.Theorem.Vocabulary

namespace SquigglyLine

open MeasureTheory Real

/-! ## Helper functions -/

/-- The curve drawn by one frequency and one phase.

    def DRAW_SINE_CURVE(amplitude, frequency, phase):
        return lambda x: amplitude * sin(frequency * x + phase)
-/
noncomputable abbrev DRAW_SINE_CURVE
    (amplitude frequency : ℝ)
    (phase : SinePhase amplitude frequency) : RealFunction :=
  (MAKE_RANDOM_PHASE_SINE amplitude frequency).eval phase

/-- The nearest distance, averaged over the data and the random phase.

    def GET_AVERAGE_DISTANCE(amplitude, data_distribution, frequency):
        return mean(
            GET_NEAREST_DISTANCE(
                DRAW_SINE_CURVE(amplitude, frequency, phase), data_point)
            for data_point in data_distribution
            for phase in uniform(0, 2 * PI))
-/
noncomputable abbrev GET_AVERAGE_DISTANCE
    (amplitude : ℝ)
    (data_distribution : DataDistribution)
    (frequency : ℝ) : ℝ :=
  (MAKE_RANDOM_PHASE_SINE amplitude frequency).expected
    GET_NEAREST_DISTANCE data_distribution

/-- The loss, averaged over the data and the random phase.

    def GET_AVERAGE_LOSS(amplitude, loss_fn, data_distribution, frequency):
        return mean(
            GET_RESIDUAL_LOSS(loss_fn)(
                DRAW_SINE_CURVE(amplitude, frequency, phase), data_point)
            for data_point in data_distribution
            for phase in uniform(0, 2 * PI))
-/
noncomputable abbrev GET_AVERAGE_LOSS
    (amplitude : ℝ)
    (loss_fn : RealFunction)
    (data_distribution : DataDistribution)
    (frequency : ℝ) : ℝ :=
  (MAKE_RANDOM_PHASE_SINE amplitude frequency).expected
    (GET_RESIDUAL_LOSS loss_fn) data_distribution

/-! ## The theorem -/

/-- **The squiggly line theorem (for sines).** A squigglier curve is closer
to the data, at rate `1 / frequency` and all the way to zero. No regression
loss sees this at the start, and a shift of the input no larger than that
distance turns it into an exact fit. -/
theorem squiggly_line_theorem
    -- Given: the height of the sine.
    (amplitude : ℝ)
    -- Given: a loss on the residual, such as `r ^ 2` or `|r|`.
    {loss_fn : RealFunction}
    (loss_is_measurable : Measurable loss_fn)  -- so its average exists; every loss in common use passes
    -- Given: the data, as a distribution over `(x, y)` pairs.
    {data_distribution : DataDistribution}
    [IsProbabilityMeasure data_distribution]   -- the probabilities add up to 1
    -- Given: the labels lie in the band the sine sweeps.
    (labels_in_band :
      ARE_LABELS_ALMOST_SURELY_IN_BAND amplitude data_distribution) :

    -- Claim 1: the distance is squeezed between two bounds.
    let claim_1_distance_is_squeezed : Prop :=
      HOLDS_FOR_EVERY_SINE amplitude fun frequency phase =>
        ∀ data_point : DataPoint ℝ,
          let curve            := DRAW_SINE_CURVE amplitude frequency phase
          let vertical_error   := GET_VERTICAL_ERROR curve data_point    -- orange line in the graph: what training sees
          let nearest_distance := GET_NEAREST_DISTANCE curve data_point  -- blue line in the graph: what the eye sees
          let slope_bound      := √(1 + (amplitude * frequency) ^ 2)     -- Pythagoras: 1 across, amplitude * frequency up (steepest slope)
          let lower_bound      := vertical_error / slope_bound           -- a curve no steeper than that cannot pass any closer
          let upper_bound      := PI / frequency                         -- half a wave: within it the sine passes every height
          let label_is_in_band :=
            IS_IN_SINE_BAND amplitude (GET_LABEL data_point)             -- a sine never leaves its band
          let is_above_lower_bound := lower_bound ≤ nearest_distance
          let is_below_upper_bound := nearest_distance ≤ upper_bound
          label_is_in_band →
            is_above_lower_bound ∧ is_below_upper_bound

    -- Claim 2: the average distance goes to zero.
    let claim_2_distance_vanishes : Prop :=
      GOES_TO_ZERO_AS_INPUT_GROWS fun frequency =>  -- it is at most PI / frequency, by claim 1
        GET_AVERAGE_DISTANCE amplitude data_distribution frequency

    -- Claim 3: the average loss is the same at every frequency.
    let claim_3_loss_is_flat : Prop :=
      ∀ frequency other_frequency : ℝ,
        let loss_here :=
          GET_AVERAGE_LOSS amplitude loss_fn data_distribution
            frequency
        let loss_there :=
          GET_AVERAGE_LOSS amplitude loss_fn data_distribution
            other_frequency
        loss_here = loss_there  -- a new frequency only shifts the phase, and a random phase stays random

    -- Claim 4: a small shift of the input fits any target in the band.
    let claim_4_warp_fits_any_target : Prop :=
      HOLDS_FOR_EVERY_SINE amplitude fun frequency phase =>
        ∀ target : RealFunction,
          let curve     := DRAW_SINE_CURVE amplitude frequency phase
          let max_shift := PI / frequency  -- the same half wave as in claim 1
          let target_stays_in_band :=
            ∀ input, IS_IN_SINE_BAND amplitude (target input)
          target_stays_in_band → ∃ warp : Warp,  -- each input goes to a nearby one where the sine is at the target's height
            let moves_each_input_a_little :=
              ∀ input, dist input (warp input) ≤ max_shift
            let hits_the_target :=
              ∀ input, curve (warp input) = target input
            moves_each_input_a_little ∧ hits_the_target

    -- The theorem: all four claims hold.
    claim_1_distance_is_squeezed ∧
    claim_2_distance_vanishes ∧
    claim_3_loss_is_flat ∧
    claim_4_warp_fits_any_target := by

  -- Bring the four claims into scope.
  intro claim_1_distance_is_squeezed claim_2_distance_vanishes
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
