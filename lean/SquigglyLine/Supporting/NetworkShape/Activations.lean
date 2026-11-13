/-
Activations and caps on slope.

Four small facts about how the pieces of a network treat slope.

* A sigmoid's slope is never above one quarter, so `layer_count` sigmoid
  layers shrink a difference by `4 ^ layer_count` unless the weights make up
  for it. That is the saturation that ReLU was brought in to avoid.
* A leaky ReLU keeps a slope of at least its leak, so it never merges two
  inputs and never goes dead.
* The higher of two lines (max pooling) is no steeper than the steeper one.
* A layer divided by its own size (spectral normalisation) has slope at most
  one.

| Name                    | Meaning                                         |
|-------------------------|-------------------------------------------------|
| `APPLY_LEAKY_RELU`      | `max(input, leak * input)`                      |
| `NORMALIZE_SPECTRALLY`  | a layer divided by its own size                 |

Theorems: `sigmoid_mul_one_sub_le`, `lipschitzWith_sigmoid`,
`lipschitzWith_iterate_sigmoid`, `leakyRelu_sub_le`, `le_leakyRelu_sub`,
`strictMono_leakyRelu`, `lipschitzWith_max`, `norm_spectralNormalize_le`,
`norm_spectralNormalize`, `lipschitzWith_spectralNormalize`.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import SquigglyLine.Style
import SquigglyLine.Theorem.Sandwich

namespace SquigglyLine

open Real NNReal

/-- The slope of a sigmoid, `sigmoid * (1 - sigmoid)`, is at most one
quarter. -/
theorem sigmoid_mul_one_sub_le
    (input : ℝ) :
    let slope   := sigmoid input * (1 - sigmoid input)
    let quarter : ℝ := 1 / 4  -- the product `s * (1 - s)` peaks at `s = 1 / 2`
    slope ≤ quarter := by
  unfold_named_pieces
  nlinarith [sq_nonneg (sigmoid input - 1 / 2)]

/-- **A sigmoid is never steeper than one quarter.** -/
theorem lipschitzWith_sigmoid :
    let slope_limit : SlopeLimit := 1 / 4  -- the biggest value of the sigmoid's slope
    LipschitzWith slope_limit sigmoid := by
  unfold_named_pieces
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun input => (hasDerivAt_sigmoid input).differentiableAt) fun input => ?_
  rw [(hasDerivAt_sigmoid input).deriv, ← NNReal.coe_le_coe, coe_nnnorm,
    Real.norm_eq_abs]
  have slope_nonneg : 0 ≤ sigmoid input * (1 - sigmoid input) :=
    mul_nonneg (sigmoid_pos input).le
      (sub_nonneg.mpr (sigmoid_lt_one input).le)
  rw [abs_of_nonneg slope_nonneg]
  have slope_le_quarter := sigmoid_mul_one_sub_le input
  simpa using slope_le_quarter

/-- **Sigmoid layers shrink differences.** `layer_count` sigmoids in a row have
slope at most `(1 / 4) ^ layer_count`. -/
theorem lipschitzWith_iterate_sigmoid
    (layer_count : ℕ) :
    let stack_slope_limit : SlopeLimit := (1 / 4) ^ layer_count  -- each sigmoid shrinks by at least 4
    let stack := sigmoid^[layer_count]
    LipschitzWith stack_slope_limit stack := by
  unfold_named_pieces
  have one_layer : LipschitzWith (1 / 4) sigmoid := lipschitzWith_sigmoid
  exact one_layer.iterate layer_count

/-- A leaky ReLU: the input where it is positive, and a share `leak` of it
where it is not.
Python: `max(input, leak * input)`. -/
def APPLY_LEAKY_RELU
    (leak : ℝ)
    (input : ℝ) : ℝ :=
  max input (leak * input)

variable {leak : ℝ}

/-- A leaky ReLU is no steeper than one. -/
theorem leakyRelu_sub_le
    (leak_le_one : leak ≤ 1)
    {input : ℝ}
    {other_input : ℝ}
    (input_le_other : input ≤ other_input) :
    let output_gap := APPLY_LEAKY_RELU leak other_input
                      - APPLY_LEAKY_RELU leak input
    let input_gap  := other_input - input
    output_gap ≤ input_gap := by
  unfold_named_pieces
  simp only [APPLY_LEAKY_RELU, max_def]
  split_ifs <;> nlinarith

/-- **A leaky ReLU keeps a slope of at least its leak.** -/
theorem le_leakyRelu_sub
    (leak_le_one : leak ≤ 1)
    {input : ℝ}
    {other_input : ℝ}
    (input_le_other : input ≤ other_input) :
    let input_gap  := other_input - input
    let least_gap  := leak * input_gap  -- the leaky side still passes a `leak` share
    let output_gap := APPLY_LEAKY_RELU leak other_input
                      - APPLY_LEAKY_RELU leak input
    least_gap ≤ output_gap := by
  unfold_named_pieces
  simp only [APPLY_LEAKY_RELU, max_def]
  split_ifs <;> nlinarith

/-- With a positive leak it is always rising: it merges no two inputs and is
never dead. -/
theorem strictMono_leakyRelu
    (leak_pos : 0 < leak)
    (leak_le_one : leak ≤ 1) :
    let layer := APPLY_LEAKY_RELU leak
    StrictMono layer := by
  unfold_named_pieces
  intro input other_input input_lt_other
  have gap_bound :
      leak * (other_input - input)
        ≤ APPLY_LEAKY_RELU leak other_input - APPLY_LEAKY_RELU leak input :=
    le_leakyRelu_sub leak_le_one input_lt_other.le
  have gap_pos : 0 < leak * (other_input - input) :=
    mul_pos leak_pos (sub_pos.mpr input_lt_other)
  linarith

/-- **Pooling never steepens.** The higher of two lines is no steeper than the
steeper of them. -/
theorem lipschitzWith_max
    {Inputs : Type*} [PseudoEMetricSpace Inputs]
    {slope_limit : SlopeLimit}
    {model : Model Inputs}
    {other_model : Model Inputs}
    (model_is_bounded : LipschitzWith slope_limit model)
    (other_is_bounded : LipschitzWith slope_limit other_model) :
    let pooled_model : Model Inputs :=
      fun input => max (model input) (other_model input)
    LipschitzWith slope_limit pooled_model := by
  unfold_named_pieces
  have pooled_bounded := model_is_bounded.max other_is_bounded
  rwa [max_self] at pooled_bounded

variable {Inputs Outputs : Type*}
  [NormedAddCommGroup Inputs] [NormedSpace ℝ Inputs]
  [NormedAddCommGroup Outputs] [NormedSpace ℝ Outputs]

/-- Spectral normalisation: a layer divided by its own size.
Python: `weights / norm(weights)`. -/
noncomputable def NORMALIZE_SPECTRALLY
    (weights : Inputs →L[ℝ] Outputs) : Inputs →L[ℝ] Outputs :=
  ‖weights‖⁻¹ • weights

/-- After spectral normalisation a layer has size at most one. -/
theorem norm_spectralNormalize_le
    (weights : Inputs →L[ℝ] Outputs) :
    let size := ‖NORMALIZE_SPECTRALLY weights‖  -- kept whole: naming the layer first changes how Lean reads the norm
    let unit_size : ℝ := 1
    size ≤ unit_size := by
  unfold_named_pieces
  rw [NORMALIZE_SPECTRALLY, norm_smul, norm_inv, norm_norm]
  rcases eq_or_ne ‖weights‖ 0 with size_zero | size_ne_zero
  · rw [size_zero]; simp
  · rw [inv_mul_cancel₀ size_ne_zero]

/-- For a layer that is not zero, the size is exactly one. -/
theorem norm_spectralNormalize
    {weights : Inputs →L[ℝ] Outputs}
    (weights_ne_zero : weights ≠ 0) :
    let size := ‖NORMALIZE_SPECTRALLY weights‖  -- kept whole: naming the layer first changes how Lean reads the norm
    let unit_size : ℝ := 1
    size = unit_size := by
  unfold_named_pieces
  rw [NORMALIZE_SPECTRALLY, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr weights_ne_zero)]

/-- **A spectrally normalised layer has slope at most one.** -/
theorem lipschitzWith_spectralNormalize
    (weights : Inputs →L[ℝ] Outputs) :
    let slope_limit : SlopeLimit := 1
    LipschitzWith slope_limit (NORMALIZE_SPECTRALLY weights) := by
  unfold_named_pieces
  refine (NORMALIZE_SPECTRALLY weights).lipschitzWith.weaken ?_
  rw [← NNReal.coe_le_coe]
  have size_le_one : ‖NORMALIZE_SPECTRALLY weights‖ ≤ 1 :=
    norm_spectralNormalize_le weights
  exact size_le_one

end SquigglyLine
