/-
Counting: why a count is hard for a model made of averages and slopes.

A count is a step: it is a whole number, and it jumps. Four facts say why
that is the worst kind of function for the models in this project.

* A read-out that changes smoothly from `count` to `count + 1` says
  `count + 1/2` somewhere on the way.
* An attention head that scores two examples equally returns the point half
  way between them, and so does the ideal denoiser at a noisy input equally
  far from two training examples.
* A model that says `count` at one input and `count + 1` at another has slope
  at least one over their distance.

The fourth fact, that a stack of local layers cannot see the whole input, is
`iterate_convolution_congr` in `Convolution.lean`.

These show that counting is hard for such models. They do not show that
this is why a real image model draws the wrong number of fingers.

Theorems:

* `exists_half_count`              a smooth read-out from `count` to
                                   `count + 1` passes through `count + 1/2`;
* `attend_two_of_const_score`      equal scores give the midpoint of the two
                                   values;
* `denoiser_two_of_equidistant`    the ideal denoiser at an input equally far
                                   from two examples returns their midpoint;
* `one_le_slope_mul_dist_of_count` a jump of one needs slope at least one over
                                   the distance.
-/
import Mathlib.Topology.Order.IntermediateValue
import SquigglyLine.Supporting.NewInputs.Averaging

namespace SquigglyLine

/-- **Between two counts there is a half.** A read-out that is continuous along
a path, and says `count` at one end and `count + 1` at the other, says
`count + 1/2` somewhere on the path. -/
theorem exists_half_count
    {readout : RealFunction}
    {count : ℝ}
    (readout_is_continuous : ContinuousOn readout (Set.Icc 0 1))
    (readout_at_start : readout 0 = count)
    (readout_at_end : readout 1 = count + 1) :
    ∃ fraction ∈ Set.Icc (0 : ℝ) 1,
      let half_count := count + 1 / 2
      readout fraction = half_count := by
  unfold_named_pieces
  -- Half a step up lies between the two ends, so the read-out hits it.
  have half_between : count + 1 / 2 ∈ Set.Icc (readout 0) (readout 1) := by
    rw [readout_at_start, readout_at_end]
    constructor <;> linarith
  obtain ⟨fraction, fraction_in_path, readout_hits_half⟩ :=
    intermediate_value_Icc zero_le_one readout_is_continuous half_between
  exact ⟨fraction, fraction_in_path, readout_hits_half⟩

variable {Space : Type*} [NormedAddCommGroup Space] [InnerProductSpace ℝ Space]

/-- An attention head that scores two examples equally returns the point half
way between them. -/
theorem attend_two_of_const_score
    (equal_score : ℝ)
    (values : Fin 2 → Space) :
    let scores : Fin 2 → ℝ := fun _ => equal_score
    let output   := ATTEND scores values
    let midpoint := (1 / 2 : ℝ) • (values 0 + values 1)  -- half of each value
    output = midpoint := by
  unfold_named_pieces
  have plain_average :
      ATTEND (fun _ : Fin 2 => equal_score) values
        = (Fintype.card (Fin 2) : ℝ)⁻¹ • ∑ i, values i :=
    attend_of_const_score equal_score values
  rw [plain_average, Fin.sum_univ_two, Fintype.card_fin]
  norm_num

/-- **The ideal denoiser blends counts.** At a noisy input equally far from two
training examples, it returns the point half way between them: half of one hand
and half of the other. -/
theorem denoiser_two_of_equidistant
    (noise_level : ℝ)
    (examples : Fin 2 → Space)
    {noisy_input : Space}
    (equidistant :
      ‖noisy_input - examples 1‖ = ‖noisy_input - examples 0‖) :
    let denoised := DENOISE_IDEALLY noise_level examples noisy_input
    let midpoint := (1 / 2 : ℝ) • (examples 0 + examples 1)  -- half of each example
    denoised = midpoint := by
  unfold_named_pieces
  have same_distance :
      ∀ i : Fin 2, ‖noisy_input - examples i‖ = ‖noisy_input - examples 0‖ :=
    Fin.forall_fin_two.mpr ⟨rfl, equidistant⟩
  -- Equal distances give equal scores, so attention is the plain average.
  have equal_scores :
      (fun i : Fin 2 => -‖noisy_input - examples i‖ ^ 2 / (2 * noise_level ^ 2))
        = fun _ =>
          -‖noisy_input - examples 0‖ ^ 2 / (2 * noise_level ^ 2) := by
    funext i
    rw [same_distance i]
  rw [DENOISE_IDEALLY, equal_scores]
  exact attend_two_of_const_score _ examples

/-- **Being sharp about a count costs slope.** A model that says `count` at one
input and `count + 1` at another has slope at least one over the distance
between them. -/
theorem one_le_slope_mul_dist_of_count
    {Inputs : Type*} [PseudoMetricSpace Inputs]
    {model : Model Inputs}
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit model)
    {input other_input : Inputs}
    {count : ℝ}
    (model_at_input : model input = count)
    (model_at_other_input : model other_input = count + 1) :
    let output_change     := (1 : ℝ)  -- from `count` to `count + 1`
    let max_output_change := slope_limit * dist input other_input
    output_change ≤ max_output_change := by
  unfold_named_pieces
  have output_gap := slope_is_bounded.dist_le_mul input other_input
  rw [Real.dist_eq, model_at_input, model_at_other_input] at output_gap
  have gap_is_one : |count - (count + 1)| = 1 := by
    rw [show count - (count + 1) = -1 by ring]
    simp
  linarith

end SquigglyLine
