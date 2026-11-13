/-
The Fourier lift: winding the input round a circle.

The lift `input ↦ (cos (frequency * input), sin (frequency * input))` winds
the line round the unit circle, `frequency` times as fast as the input
moves. A flat plane over that circle is a sine wave downstairs.

| Name               | Meaning                                              |
|--------------------|------------------------------------------------------|
| `CosineSinePair`   | a point of the plane: a cosine part and a sine part  |
| `LIFT_BY_FOURIER`  | the lift: the input, wound round the unit circle     |

Theorems:

* `liftedModel_fourierLift` : weights `(cosine_weight, sine_weight)` give
  `cosine_weight * cos (frequency * input)
    + sine_weight * sin (frequency * input)`.
* `liftKernel_fourierLift` : the kernel of two inputs is
  `cos (frequency * (input - other_input))`. It depends only on how far
  apart they are.
* `norm_fourierLift_sub_sq` : two lifted points are
  `√(2 - 2 cos (frequency * (input - other_input)))` apart.
* `lipschitzWith_fourierLift` : so the lift stretches distances by at most
  `|frequency|`.
* `lipschitzWith_liftedModel_fourierLift` : and the wave is no steeper than
  the size of its weights times the frequency.

Shift invariance, for any lift:
* `liftedModel_shift` : if the kernel depends only on how far apart two inputs
  are, shifting the data and the question together changes no answer.
* `liftKernel_fourierLift_shift` : the Fourier lift is such a lift.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import SquigglyLine.Networks.Lift

namespace SquigglyLine

open NNReal

/-- A point of the plane, written `!₂[cosine_part, sine_part]`, with the
usual length `√(cosine_part² + sine_part²)`.
Python: `tuple[float, float]`. -/
abbrev CosineSinePair := EuclideanSpace ℝ (Fin 2)

/-! ### The lift -/

/-- Wind the input round the unit circle at the given frequency.
Python: `(cos(frequency * input), sin(frequency * input))`. -/
noncomputable def LIFT_BY_FOURIER
    (frequency : ℝ)
    (input : ℝ) : CosineSinePair :=
  let angle := frequency * input        -- how far round the circle the input has gone
  !₂[Real.cos angle, Real.sin angle]    -- the point of the unit circle at that angle

/-- **A flat plane over the circle is a wave.** -/
theorem liftedModel_fourierLift
    (frequency : ℝ)
    (cosine_weight : ℝ)
    (sine_weight : ℝ)
    (input : ℝ) :
    let features := LIFT_BY_FOURIER frequency
    let weights : CosineSinePair := !₂[cosine_weight, sine_weight]
    let output   := EVALUATE_LIFTED_MODEL features weights input
    let angle    := frequency * input
    let wave     :=
      cosine_weight * Real.cos angle + sine_weight * Real.sin angle  -- the dot product of the weights with (cos, sin)
    output = wave := by
  unfold_named_pieces
  simp [EVALUATE_LIFTED_MODEL, LIFT_BY_FOURIER, PiLp.inner_apply,
    Fin.sum_univ_two, mul_comm]

/-- **The kernel sees only the gap.** The overlap of two lifted inputs is the
cosine of the frequency times how far apart they are. -/
theorem liftKernel_fourierLift
    (frequency : ℝ)
    (input : ℝ)
    (other_input : ℝ) :
    let features := LIFT_BY_FOURIER frequency
    let kernel   := GET_LIFT_KERNEL features input other_input
    let gap      := input - other_input
    let cosine_of_the_turn := Real.cos (frequency * gap)  -- two arrows of length 1 overlap by the cosine of the angle between them
    kernel = cosine_of_the_turn := by
  unfold_named_pieces
  simp [GET_LIFT_KERNEL, LIFT_BY_FOURIER, PiLp.inner_apply, Fin.sum_univ_two,
    mul_sub, Real.cos_sub, mul_comm]

/-- Shifting both inputs by the same amount leaves the Fourier kernel as it
was: the gap between them has not changed. -/
theorem liftKernel_fourierLift_shift
    (frequency : ℝ)
    (shift : ℝ)
    (input : ℝ)
    (other_input : ℝ) :
    let features       := LIFT_BY_FOURIER frequency
    let shifted_kernel :=
      GET_LIFT_KERNEL features (input + shift) (other_input + shift)
    let kernel         := GET_LIFT_KERNEL features input other_input
    shifted_kernel = kernel := by
  unfold_named_pieces
  rw [liftKernel_fourierLift, liftKernel_fourierLift,
    add_sub_add_right_eq_sub]

/-! ### Its stretch -/

/-- The squared distance between two lifted inputs: the squared length of a
chord of the unit circle. -/
theorem norm_fourierLift_sub_sq
    (frequency : ℝ)
    (input : ℝ)
    (other_input : ℝ) :
    let lifted_input     := LIFT_BY_FOURIER frequency input
    let lifted_other     := LIFT_BY_FOURIER frequency other_input
    let squared_distance := ‖lifted_input - lifted_other‖ ^ 2
    let gap              := input - other_input
    let squared_chord    := 2 - 2 * Real.cos (frequency * gap)  -- law of cosines, two sides of length 1: 1 + 1 - 2 cos(angle)
    squared_distance = squared_chord := by
  unfold_named_pieces
  have overlap_is_cosine (first second : ℝ) :
      inner ℝ (LIFT_BY_FOURIER frequency first)
          (LIFT_BY_FOURIER frequency second)
        = Real.cos (frequency * (first - second)) :=
    liftKernel_fourierLift frequency first second
  -- Multiply the square out into three overlaps, each one a cosine.
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, overlap_is_cosine, overlap_is_cosine,
    overlap_is_cosine, sub_self, sub_self, mul_zero, Real.cos_zero]
  ring

/-- **The Fourier lift stretches by at most its frequency.** -/
theorem lipschitzWith_fourierLift
    (frequency : ℝ) :
    let slope_limit := ‖frequency‖₊             -- the size of the frequency, kept as a number that is not negative
    let features    := LIFT_BY_FOURIER frequency
    LipschitzWith slope_limit features := by
  unfold_named_pieces
  refine LipschitzWith.of_dist_le_mul fun input other_input => ?_
  -- A cosine is never far below one: `1 - angle² / 2 ≤ cos angle`.
  have cosine_is_near_one :=
    Real.one_sub_sq_div_two_le_cos (x := frequency * (input - other_input))
  -- So the chord is no longer than the turn `|frequency| * |gap|`.
  have squared_distance_is_small :
      ‖LIFT_BY_FOURIER frequency input
          - LIFT_BY_FOURIER frequency other_input‖ ^ 2
        ≤ (|frequency| * |input - other_input|) ^ 2 := by
    rw [norm_fourierLift_sub_sq, ← abs_mul, sq_abs]
    linarith
  rw [dist_eq_norm, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    squared_distance_is_small

/-- **A wave is no steeper than its size times its frequency.** -/
theorem lipschitzWith_liftedModel_fourierLift
    (frequency : ℝ)
    (weights : CosineSinePair) :
    let slope_limit := ‖weights‖₊ * ‖frequency‖₊  -- tilt of the plane times stretch of the lift
    let wave        :=
      EVALUATE_LIFTED_MODEL (LIFT_BY_FOURIER frequency) weights
    LipschitzWith slope_limit wave :=
  lipschitzWith_liftedModel (lipschitzWith_fourierLift frequency) weights

/-! ### Shift invariance -/

section Shift

variable {Inputs Weights Examples : Type*} [Add Inputs]
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]

/-- **Shift the data and the question together and no answer changes.** This
holds whenever the kernel depends only on how far apart two inputs are. -/
theorem liftedModel_shift
    (features : FeatureMap Inputs Weights)
    (kernel_ignores_shift :
      ∀ shift input other_input,
        GET_LIFT_KERNEL features (input + shift) (other_input + shift)
          = GET_LIFT_KERNEL features input other_input)
    (examples : Finset Examples)
    (data_inputs : InputPerExample Examples Inputs)
    (coefficients : NumberPerExample Examples)
    (input : Inputs)
    (shift : Inputs) :
    let shifted_weights :=
      ∑ i ∈ examples, coefficients i • features (data_inputs i + shift)  -- weights built from the shifted data
    let weights :=
      ∑ i ∈ examples, coefficients i • features (data_inputs i)   -- weights built from the data as it was
    let shifted_answer :=
      EVALUATE_LIFTED_MODEL features shifted_weights (input + shift)
    let answer := EVALUATE_LIFTED_MODEL features weights input
    shifted_answer = answer := by
  unfold_named_pieces
  -- The kernel trick, once for the shifted data and once for the plain
  -- data. Both answers are then sums of kernels, and the kernels agree.
  have shifted_answer_by_kernel :=
    liftedModel_add_sum features examples 0
      (fun i => data_inputs i + shift) coefficients (input + shift)
  have answer_by_kernel :=
    liftedModel_add_sum features examples 0 data_inputs coefficients input
  simp only [zero_add] at shifted_answer_by_kernel answer_by_kernel
  rw [shifted_answer_by_kernel, answer_by_kernel]
  simp only [kernel_ignores_shift, EVALUATE_LIFTED_MODEL, inner_zero_left]

end Shift

end SquigglyLine
