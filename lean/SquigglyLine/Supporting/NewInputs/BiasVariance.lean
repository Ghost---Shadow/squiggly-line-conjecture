/-
Bias and variance, and what the dial is.

A fit's answer at a new input is off by a fixed part (the bias) and a part
that follows the noise. A floor `floor` is added to the strength of every
direction.

* `bias_variance` : if the noise part is zero on average, the expected squared
  error is the bias squared plus the variance.
* `signal_term_sub` : the bias. A floor shrinks the signal term by the factor
  `floor / (signal_strength + floor)`.
* `expected_sq_error` : the two together, for a signal along a direction of
  strength `signal_strength` and noise along one of strength
  `noise_strength`.
* `bias_factor_mono` : raising the floor raises the bias.
* `variance_factor_anti` : raising the floor lowers the variance.

| Name                   | Meaning                                          |
|------------------------|--------------------------------------------------|
| `GET_BIAS_FACTOR`      | `floor / (signal_strength + floor)`              |
| `NoiseTerm Outcomes`   | a number that depends on the draw of the noise   |
| `signal_overlap`       | how much of the signal the new input picks up    |
| `noise_overlap`        | how much of the noise the new input picks up     |
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import SquigglyLine.Style

namespace SquigglyLine

open MeasureTheory

/-! ### Types and helper functions -/

/-- A number that depends on the random draw of the noise.
Python: `Callable[[Outcome], float]`. -/
abbrev NoiseTerm (Outcomes : Type*) := Outcomes → ℝ

/-- The part of the signal term that a floor takes away: none of it with no
floor, nearly all of it with a high floor.
Python: `floor / (signal_strength + floor)`. -/
noncomputable abbrev GET_BIAS_FACTOR
    (signal_strength : ℝ)
    (floor : ℝ) : ℝ :=
  floor / (signal_strength + floor)

/-! ### The two factors -/

section Factors

/-- **The bias.** A floor shrinks the signal term by the factor
`floor / (signal_strength + floor)`. -/
theorem signal_term_sub
    (signal_overlap : ℝ)
    {signal_strength : ℝ}
    {floor : ℝ}
    (signal_strength_ne_zero : signal_strength ≠ 0)                -- so that the divisions below make sense
    (raised_strength_ne_zero : signal_strength + floor ≠ 0) :
    let true_signal_term   := signal_overlap / signal_strength     -- the right answer: the overlap over the strength
    let fitted_signal_term :=
      signal_overlap / (signal_strength + floor)                   -- the fit divides by the strength with the floor added
    let bias_factor        := GET_BIAS_FACTOR signal_strength floor
    fitted_signal_term - true_signal_term
      = -(true_signal_term * bias_factor) := by                    -- minus: the floor pulls the answer towards zero
  unfold_named_pieces
  field_simp
  ring

/-- **Raising the floor raises the bias.** -/
theorem bias_factor_mono
    {signal_strength : ℝ}
    {lower_floor : ℝ}
    {higher_floor : ℝ}
    (signal_strength_pos : 0 < signal_strength)
    (lower_floor_nonneg : 0 ≤ lower_floor)
    (floor_is_raised : lower_floor ≤ higher_floor) :
    let bias_factor_before := GET_BIAS_FACTOR signal_strength lower_floor
    let bias_factor_after  := GET_BIAS_FACTOR signal_strength higher_floor
    bias_factor_before ≤ bias_factor_after := by
  unfold_named_pieces
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Raising the floor lowers the variance.** -/
theorem variance_factor_anti
    {noise_strength : ℝ}
    {lower_floor : ℝ}
    {higher_floor : ℝ}
    (noise_strength_nonneg : 0 ≤ noise_strength)
    (lower_floor_pos : 0 < lower_floor)
    (floor_is_raised : lower_floor ≤ higher_floor) :
    let variance_factor_before := 1 / (noise_strength + lower_floor)  -- the noise is divided by its raised strength
    let variance_factor_after  := 1 / (noise_strength + higher_floor)
    variance_factor_after ≤ variance_factor_before := by
  unfold_named_pieces
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

end Factors

/-! ### They add -/

section Split

variable {Outcomes : Type*} [MeasurableSpace Outcomes]
  (noise_distribution : Measure Outcomes)
  [IsProbabilityMeasure noise_distribution]

/-- **Bias squared plus variance.** If `noise_part` is zero on average, the
expected square of `bias + noise_part` is `bias ^ 2` plus the expected square
of `noise_part`. -/
theorem bias_variance
    {noise_part : NoiseTerm Outcomes}
    (noise_part_has_mean : Integrable noise_part noise_distribution)  -- `Integrable`: its average exists
    (noise_part_sq_has_mean :
      Integrable (fun outcome => noise_part outcome ^ 2)
        noise_distribution)
    (noise_part_mean_zero :
      ∫ outcome, noise_part outcome ∂noise_distribution = 0)       -- `∫ ... ∂`: the average over the draws of the noise
    (bias : ℝ) :
    let mean_squared_error :=
      ∫ outcome, (bias + noise_part outcome) ^ 2 ∂noise_distribution
    let variance           :=
      ∫ outcome, noise_part outcome ^ 2 ∂noise_distribution        -- the mean is zero, so the mean square is the variance
    mean_squared_error = bias ^ 2 + variance := by                 -- the cross term `2 * bias * noise_part` averages to zero
  unfold_named_pieces
  -- Multiply the square out, then average the three terms one at a time.
  have square_multiplied_out :
      (fun outcome => (bias + noise_part outcome) ^ 2)
        = fun outcome =>
          bias ^ 2 + 2 * bias * noise_part outcome
            + noise_part outcome ^ 2 := by
    funext outcome
    ring
  have cross_term_has_mean :
      Integrable (fun outcome => 2 * bias * noise_part outcome)
        noise_distribution :=
    noise_part_has_mean.const_mul _
  have bias_sq_has_mean :
      Integrable (fun _ : Outcomes => bias ^ 2) noise_distribution :=
    integrable_const _
  have split_off_noise_square :
      ∫ outcome, bias ^ 2 + 2 * bias * noise_part outcome
          + noise_part outcome ^ 2 ∂noise_distribution
        = (∫ outcome, bias ^ 2 + 2 * bias * noise_part outcome
            ∂noise_distribution)
          + ∫ outcome, noise_part outcome ^ 2 ∂noise_distribution :=
    integral_add (bias_sq_has_mean.add cross_term_has_mean)
      noise_part_sq_has_mean
  have split_off_cross_term :
      ∫ outcome, bias ^ 2 + 2 * bias * noise_part outcome
          ∂noise_distribution
        = (∫ _outcome, bias ^ 2 ∂noise_distribution)
          + ∫ outcome, 2 * bias * noise_part outcome
              ∂noise_distribution :=
    integral_add bias_sq_has_mean cross_term_has_mean
  rw [square_multiplied_out, split_off_noise_square, split_off_cross_term,
    integral_const_mul, noise_part_mean_zero]
  simp

/-- **The split for a signal and a noise.** The signal has overlap
`signal_overlap` with the new input and lies along a direction of strength
`signal_strength`. The noise has overlap `noise_overlap`, a random number that
is zero on average, and lies along a direction of strength `noise_strength`.
With a floor `floor`, the expected squared error at the new input is the bias
squared plus the variance. -/
theorem expected_sq_error
    {noise_overlap : NoiseTerm Outcomes}
    (noise_overlap_has_mean : Integrable noise_overlap noise_distribution)
    (noise_overlap_sq_has_mean :
      Integrable (fun outcome => noise_overlap outcome ^ 2)
        noise_distribution)
    (noise_overlap_mean_zero :
      ∫ outcome, noise_overlap outcome ∂noise_distribution = 0)
    (signal_overlap : ℝ)
    {signal_strength : ℝ}
    {noise_strength : ℝ}
    {floor : ℝ}
    (signal_strength_ne_zero : signal_strength ≠ 0)
    (raised_strength_ne_zero : signal_strength + floor ≠ 0) :
    let true_answer        := signal_overlap / signal_strength
    let fitted_signal_term :=
      signal_overlap / (signal_strength + floor)
    let mean_squared_error :=
      ∫ outcome,
        (fitted_signal_term
          + noise_overlap outcome / (noise_strength + floor)       -- the noise, divided by its raised strength
          - true_answer) ^ 2 ∂noise_distribution
    let bias_size          :=
      true_answer * GET_BIAS_FACTOR signal_strength floor          -- from `signal_term_sub`; the sign goes when squared
    let noise_mean_square  :=
      ∫ outcome, noise_overlap outcome ^ 2 ∂noise_distribution
    let variance           :=
      noise_mean_square / (noise_strength + floor) ^ 2             -- dividing a number by `c` divides its mean square by `c ^ 2`
    mean_squared_error = bias_size ^ 2 + variance := by
  unfold_named_pieces
  -- The error is a fixed part, the bias, plus a part that follows the noise.
  have error_is_bias_plus_noise :
      (fun outcome =>
        (signal_overlap / (signal_strength + floor)
          + noise_overlap outcome / (noise_strength + floor)
          - signal_overlap / signal_strength) ^ 2)
        = fun outcome =>
          (-(signal_overlap / signal_strength
              * (floor / (signal_strength + floor)))
            + noise_overlap outcome / (noise_strength + floor)) ^ 2 := by
    funext outcome
    rw [← signal_term_sub signal_overlap signal_strength_ne_zero
      raised_strength_ne_zero]
    ring
  have noise_part_has_mean :
      Integrable (fun outcome =>
        noise_overlap outcome / (noise_strength + floor))
        noise_distribution :=
    noise_overlap_has_mean.div_const _
  have noise_part_sq_has_mean :
      Integrable (fun outcome =>
        (noise_overlap outcome / (noise_strength + floor)) ^ 2)
        noise_distribution := by
    simp_rw [div_pow]
    exact noise_overlap_sq_has_mean.div_const _
  have noise_part_mean_zero :
      ∫ outcome, noise_overlap outcome / (noise_strength + floor)
        ∂noise_distribution = 0 := by
    rw [integral_div, noise_overlap_mean_zero, zero_div]
  rw [error_is_bias_plus_noise,
    bias_variance noise_distribution noise_part_has_mean
      noise_part_sq_has_mean noise_part_mean_zero,
    neg_sq]
  simp_rw [div_pow]
  rw [integral_div]

end Split

end SquigglyLine
