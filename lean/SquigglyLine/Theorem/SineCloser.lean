/-
The conjecture, settled for sines.

A sine of frequency `frequency` takes every value of its band within
`PI / frequency` of every input. So its nearest-point distance to in-band
data is at most `PI / frequency`, for every phase, and goes to zero as the
frequency grows. That is the geometric half of the conjecture, as a theorem.

`closer_but_no_better` puts it next to `Verdict.lean`: along the same family
the nearest-point distance goes to zero while every regression loss stays
exactly where it was.

Theorems:

* `sin_coversWithin`               a sine reaches every height within half a
                                   wave;
* `sin_exists_phaseShift`          or after a phase shift of half a turn;
* `sineWave_eval_coe`              the random-phase sine is the usual sine;
* `sineWave_coversWithin`          so every draw covers its band;
* `lipschitzWith_sine`             a sine's slope is at most
                                   `|amplitude| * |frequency|`;
* `sineWave_nearestDist_bounds`    the distance, pinned from both sides;
* `sineWave_exists_warp`           a small warp fits any in-band target;
* `expected_nearestDist_sineWave_le`, `tendsto_expected_nearestDist_sineWave`
                                   the same on average, and in the limit;
* `closer_but_no_better`           closer, at no change in loss.
-/
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import SquigglyLine.Theorem.Oscillation
import SquigglyLine.Theorem.Verdict

namespace SquigglyLine

open MeasureTheory Filter Topology Real

/-- A real sine of frequency `frequency` takes every value in
`[-|amplitude|, |amplitude|]` within `PI / frequency` of every input. -/
theorem sin_coversWithin
    (amplitude phase : ℝ)
    {frequency : ℝ}
    (frequency_pos : 0 < frequency) :
    let sine : RealFunction := fun input =>
      amplitude * sin (frequency * input + phase)
    let half_wave := PI / frequency  -- a full wave is 2 * PI / frequency wide
    COVERS_WITHIN sine half_wave (GET_SINE_BAND amplitude) := by
  unfold_named_pieces
  intro input label label_in_band
  -- A flat line (amplitude zero) only ever takes the value zero.
  rcases eq_or_ne amplitude 0 with rfl | amplitude_ne_zero
  · have label_is_zero : label = 0 := by
      have := label_in_band.1; have := label_in_band.2; simp at *; linarith
    exact ⟨input, by simpa using (div_pos pi_pos frequency_pos).le,
      by simp [label_is_zero]⟩
  have ratio_is_a_sine_value : |label / amplitude| ≤ 1 := by
    rw [abs_div, div_le_one (abs_pos.mpr amplitude_ne_zero)]
    exact abs_le.mpr label_in_band
  obtain ⟨ratio_ge_neg_one, ratio_le_one⟩ := abs_le.mp ratio_is_a_sine_value
  -- One angle at which the sine has the right height.
  set base_angle := arcsin (label / amplitude) with base_angle_def
  -- The angle the sine is at now.
  set current_angle := frequency * input + phase with current_angle_def
  -- Every full turn gives the same height. Take the copy of `base_angle`
  -- nearest to the current angle.
  set turns : ℤ := round ((current_angle - base_angle) / (2 * π))
    with turns_def
  set target_angle := base_angle + turns * (2 * π) with target_angle_def
  have two_pi_pos : (0 : ℝ) < 2 * π := by positivity
  -- Rounding is off by at most a half, so the nearest copy is at most half
  -- a turn away.
  have angles_are_close : |current_angle - target_angle| ≤ π := by
    have rounding_error :=
      abs_sub_round ((current_angle - base_angle) / (2 * π))
    have gap_in_turns : current_angle - target_angle
        = (2 * π) * ((current_angle - base_angle) / (2 * π) - turns) := by
      rw [target_angle_def]; field_simp; ring
    rw [gap_in_turns, abs_mul, abs_of_pos two_pi_pos]
    nlinarith [abs_nonneg ((current_angle - base_angle) / (2 * π) - turns)]
  -- The input at which the sine is at `target_angle`.
  refine ⟨(target_angle - phase) / frequency, ?_, ?_⟩
  · -- Half a turn of angle is `PI / frequency` of input.
    have gap_in_input : input - (target_angle - phase) / frequency
        = (current_angle - target_angle) / frequency := by
      rw [current_angle_def]; field_simp; ring
    rw [Real.dist_eq, gap_in_input, abs_div, abs_of_pos frequency_pos]
    exact div_le_div_of_nonneg_right angles_are_close frequency_pos.le
  · have angle_there :
        frequency * ((target_angle - phase) / frequency) + phase
          = base_angle + turns * (2 * π) := by
      rw [target_angle_def]; field_simp; ring
    show amplitude
        * sin (frequency * ((target_angle - phase) / frequency) + phase)
      = label
    rw [angle_there, sin_add_int_mul_two_pi, base_angle_def,
      sin_arcsin ratio_ge_neg_one ratio_le_one]
    field_simp

/-- **Once the phase matches.** For any data point with its label in the
band, a change of phase of at most half a turn makes the sine pass through
it. The change needed does not shrink with the frequency: a squigglier sine
is closer in the input and exactly as far in the phase. -/
theorem sin_exists_phaseShift
    (amplitude phase : ℝ)
    {frequency : ℝ}
    (frequency_pos : 0 < frequency)
    (input : ℝ)
    {label : ℝ}
    (label_in_band : IS_IN_SINE_BAND amplitude label) :
    ∃ phase_shift : ℝ,
      let shift_is_small := |phase_shift| ≤ PI  -- half a turn, whatever the frequency
      let shifted_sine_hits_the_label :=
        amplitude * sin (frequency * input + (phase + phase_shift)) = label
      shift_is_small ∧ shifted_sine_hits_the_label := by
  unfold_named_pieces
  -- Moving the input by `gap` is the same as moving the phase by
  -- `frequency * gap`.
  obtain ⟨other_input, other_is_near, other_hits_label⟩ :=
    sin_coversWithin amplitude phase frequency_pos input label label_in_band
  refine ⟨frequency * (other_input - input), ?_, ?_⟩
  · rw [abs_mul, abs_of_pos frequency_pos, abs_sub_comm, ← Real.dist_eq]
    calc frequency * dist input other_input
        ≤ frequency * (π / frequency) :=
          mul_le_mul_of_nonneg_left other_is_near frequency_pos.le
      _ = π := by field_simp
  · rw [← other_hits_label]
    congr 2
    ring

/-- With the phase written as a real number, the random-phase sine is the
usual sine. -/
theorem sineWave_eval_coe
    (amplitude frequency phase : ℝ) :
    let random_phase_sine :=
      (MAKE_RANDOM_PHASE_SINE amplitude frequency).eval
        (phase : AddCircle (2 * PI))
    let usual_sine : RealFunction := fun input =>
      amplitude * sin (frequency * input + phase)
    random_phase_sine = usual_sine := by
  unfold_named_pieces
  funext input
  show amplitude * Angle.sin ((↑(frequency * input) : Angle) + (↑phase : Angle))
    = _
  rw [← Angle.coe_add, Angle.sin_coe]

/-- Every draw of the random-phase sine covers its band within
`PI / frequency`. -/
theorem sineWave_coversWithin
    (amplitude : ℝ)
    {frequency : ℝ}
    (frequency_pos : 0 < frequency)
    (phase : SinePhase amplitude frequency) :
    let sine      := (MAKE_RANDOM_PHASE_SINE amplitude frequency).eval phase
    let half_wave := PI / frequency  -- a full wave is 2 * PI / frequency wide
    COVERS_WITHIN sine half_wave (GET_SINE_BAND amplitude) := by
  unfold_named_pieces
  -- A point of the circle is some real angle, wrapped round.
  obtain ⟨real_phase, rfl⟩ :
      ∃ real_phase : ℝ, (real_phase : AddCircle (2 * π)) = phase :=
    QuotientAddGroup.mk_surjective phase
  rw [sineWave_eval_coe]
  exact sin_coversWithin amplitude real_phase frequency_pos

/-- A sine of amplitude `amplitude` and frequency `frequency` has slope at
most `|amplitude| * |frequency|`. -/
theorem lipschitzWith_sine
    (amplitude frequency phase : ℝ) :
    let sine : RealFunction := fun input =>
      amplitude * sin (frequency * input + phase)
    let slope_limit := ‖amplitude‖₊ * ‖frequency‖₊  -- the derivative is amplitude * frequency * cos(...), and |cos| ≤ 1
    LipschitzWith slope_limit sine := by
  unfold_named_pieces
  refine LipschitzWith.of_dist_le_mul fun input other_input => ?_
  -- `sin` itself never changes faster than its angle.
  have sin_gap_le_angle_gap :=
    abs_sin_sub_sin_le (frequency * input + phase)
      (frequency * other_input + phase)
  have angle_gap : frequency * input + phase - (frequency * other_input + phase)
      = frequency * (input - other_input) := by ring
  rw [angle_gap, abs_mul] at sin_gap_le_angle_gap
  simp only [Real.dist_eq, NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs]
  rw [← mul_sub, abs_mul]
  calc |amplitude| * |sin (frequency * input + phase)
          - sin (frequency * other_input + phase)|
      ≤ |amplitude| * (|frequency| * |input - other_input|) :=
        mul_le_mul_of_nonneg_left sin_gap_le_angle_gap (abs_nonneg amplitude)
    _ = |amplitude| * |frequency| * |input - other_input| := by ring

/-- **The distance for sines, pinned from both sides, at every data point
and every phase.** For a label in the band, the nearest-point distance lies
between the vertical error divided by `√(1 + (amplitude * frequency)²)` and
`PI / frequency`. Both ends fall like `1 / frequency`. -/
theorem sineWave_nearestDist_bounds
    (amplitude : ℝ)
    {frequency : ℝ}
    (frequency_pos : 0 < frequency)
    (phase : SinePhase amplitude frequency)
    (data_point : DataPoint ℝ)
    (label_in_band : IS_IN_SINE_BAND amplitude (GET_LABEL data_point)) :
    let sine := (MAKE_RANDOM_PHASE_SINE amplitude frequency).eval phase
    let vertical_error   := GET_VERTICAL_ERROR sine data_point
    let nearest_distance := GET_NEAREST_DISTANCE sine data_point
    let slope_bound      := √(1 + (amplitude * frequency) ^ 2)  -- Pythagoras: 1 across, amplitude * frequency up (steepest slope)
    let lower_bound      := vertical_error / slope_bound         -- a curve no steeper than that cannot pass any closer
    let upper_bound      := PI / frequency                       -- half a wave: within it the sine passes every height
    let is_above_lower_bound := lower_bound ≤ nearest_distance
    let is_below_upper_bound := nearest_distance ≤ upper_bound
    is_above_lower_bound ∧ is_below_upper_bound := by
  unfold_named_pieces
  -- The upper bound is the covering bound.
  refine ⟨?_, nearestDist_le_of_coversWithin
    (sineWave_coversWithin amplitude frequency_pos phase)
    data_point label_in_band⟩
  -- The lower bound is the slope sandwich, with the slope of a sine.
  obtain ⟨real_phase, rfl⟩ :
      ∃ real_phase : ℝ, (real_phase : AddCircle (2 * π)) = phase :=
    QuotientAddGroup.mk_surjective phase
  rw [sineWave_eval_coe, div_le_iff₀' (by positivity)]
  have sandwich :=
    verticalDist_le_of_lipschitz
      (lipschitzWith_sine amplitude frequency real_phase) data_point
  have slope_limit_squared :
      ((‖amplitude‖₊ * ‖frequency‖₊ : NNReal) : ℝ) ^ 2
        = (amplitude * frequency) ^ 2 := by
    simp [mul_pow]
  rwa [slope_limit_squared] at sandwich

/-- **A sine fits anything in its band, after a small warp.** Any target
with values in the band is matched exactly by the sine of frequency
`frequency` after moving each input by at most `PI / frequency`. For a
single data point this is a shift of the phase. -/
theorem sineWave_exists_warp
    (amplitude : ℝ)
    {frequency : ℝ}
    (frequency_pos : 0 < frequency)
    (phase : SinePhase amplitude frequency)
    (target : RealFunction)
    (target_stays_in_band : ∀ input, IS_IN_SINE_BAND amplitude (target input)) :
    let sine      := (MAKE_RANDOM_PHASE_SINE amplitude frequency).eval phase
    let max_shift := PI / frequency  -- half a wave
    ∃ warp : Warp,
      let moves_each_input_a_little :=
        ∀ input, dist input (warp input) ≤ max_shift
      let hits_the_target :=
        ∀ input, sine (warp input) = target input
      moves_each_input_a_little ∧ hits_the_target :=
  exists_warp_of_coversWithin
    (sineWave_coversWithin amplitude frequency_pos phase)
    target target_stays_in_band

variable {data_distribution : DataDistribution}
  [IsProbabilityMeasure data_distribution]

/-- **The average distance for sines, with a rate.** On data whose labels
lie in the band, the expected nearest-point distance of a random-phase sine
of frequency `frequency` is at most `PI / frequency`. -/
theorem expected_nearestDist_sineWave_le
    (amplitude : ℝ)
    {frequency : ℝ}
    (frequency_pos : 0 < frequency)
    (labels_in_band :
      ARE_LABELS_ALMOST_SURELY_IN_BAND amplitude data_distribution) :
    let expected_distance :=
      (MAKE_RANDOM_PHASE_SINE amplitude frequency).expected
        GET_NEAREST_DISTANCE data_distribution
    let half_wave := PI / frequency
    expected_distance ≤ half_wave :=
  expected_nearestDist_le _
    (sineWave_coversWithin amplitude frequency_pos)
    data_distribution labels_in_band

/-- **The average distance for sines, in the limit.** The expected
nearest-point distance goes to zero as the frequency grows. -/
theorem tendsto_expected_nearestDist_sineWave
    (amplitude : ℝ)
    (labels_in_band :
      ARE_LABELS_ALMOST_SURELY_IN_BAND amplitude data_distribution) :
    let expected_distance_at : RealFunction := fun frequency =>
      (MAKE_RANDOM_PHASE_SINE amplitude frequency).expected
        GET_NEAREST_DISTANCE data_distribution
    GOES_TO_ZERO_AS_INPUT_GROWS expected_distance_at :=
  -- Squeezed between zero and `PI / frequency`, which goes to zero.
  squeeze_zero'
    (Eventually.of_forall fun _ =>
      expected_nearestDist_nonneg _ data_distribution)
    ((eventually_gt_atTop 0).mono fun _ frequency_pos =>
      expected_nearestDist_sineWave_le amplitude frequency_pos labels_in_band)
    (tendsto_const_nhds.div_atTop tendsto_id)

/-- **Closer, but no better.** As the frequency of a random-phase sine
grows, its expected distance to the nearest point of the data goes to zero,
and its expected loss, for every regression loss, does not change at all. -/
theorem closer_but_no_better
    (amplitude : ℝ)
    {loss_fn : RealFunction}
    (loss_is_measurable : Measurable loss_fn)
    (labels_in_band :
      ARE_LABELS_ALMOST_SURELY_IN_BAND amplitude data_distribution) :
    let expected_distance_at : RealFunction := fun frequency =>
      (MAKE_RANDOM_PHASE_SINE amplitude frequency).expected
        GET_NEAREST_DISTANCE data_distribution
    let expected_loss_at : RealFunction := fun frequency =>
      (MAKE_RANDOM_PHASE_SINE amplitude frequency).expected
        (GET_RESIDUAL_LOSS loss_fn) data_distribution
    let distance_vanishes :=
      GOES_TO_ZERO_AS_INPUT_GROWS expected_distance_at
    let loss_is_flat :=
      ∀ frequency other_frequency : ℝ,
        expected_loss_at frequency = expected_loss_at other_frequency
    distance_vanishes ∧ loss_is_flat :=
  ⟨tendsto_expected_nearestDist_sineWave amplitude labels_in_band,
    fun frequency other_frequency =>
      expected_residualLoss_congr loss_is_measurable
        (marginal_sineWave_eq amplitude frequency other_frequency)
        data_distribution⟩

end SquigglyLine
