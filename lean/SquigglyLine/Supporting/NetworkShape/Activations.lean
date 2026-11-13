/-
Activations and caps on slope.

Four small facts about how the pieces of a network treat slope.

* A sigmoid's slope is never above one quarter, so `L` sigmoid layers shrink
  a difference by `4 ^ L` unless the weights make up for it. That is the
  saturation that ReLU was brought in to avoid.
* A leaky ReLU keeps a slope of at least its leak, so it never merges two
  inputs and never goes dead.
* The higher of two lines (max pooling) is no steeper than the steeper one.
* A layer divided by its own size (spectral normalisation) has slope at most
  one.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Definitions: `APPLY_LEAKY_RELU`, `NORMALIZE_SPECTRALLY`.

Theorems: `sigmoid_mul_one_sub_le`, `lipschitzWith_sigmoid`,
`lipschitzWith_iterate_sigmoid`, `leakyRelu_sub_le`, `le_leakyRelu_sub`,
`strictMono_leakyRelu`, `lipschitzWith_max`, `norm_spectralNormalize_le`,
`norm_spectralNormalize`, `lipschitzWith_spectralNormalize`.
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import SquigglyLine.Style

namespace SquigglyLine

open Real NNReal

/-- The slope of a sigmoid, `s * (1 - s)`, is at most one quarter. -/
theorem sigmoid_mul_one_sub_le (x : ℝ) : sigmoid x * (1 - sigmoid x) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (sigmoid x - 1 / 2)]

/-- **A sigmoid is never steeper than one quarter.** -/
theorem lipschitzWith_sigmoid : LipschitzWith (1 / 4) sigmoid := by
  refine lipschitzWith_of_nnnorm_deriv_le
    (fun x => (hasDerivAt_sigmoid x).differentiableAt) fun x => ?_
  rw [(hasDerivAt_sigmoid x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  have hpos : 0 ≤ sigmoid x * (1 - sigmoid x) :=
    mul_nonneg (sigmoid_pos x).le (sub_nonneg.mpr (sigmoid_lt_one x).le)
  rw [abs_of_nonneg hpos]
  have h := sigmoid_mul_one_sub_le x
  simpa using h

/-- **Sigmoid layers shrink differences.** `L` sigmoids in a row have slope at most
`(1 / 4) ^ L`. -/
theorem lipschitzWith_iterate_sigmoid (L : ℕ) : LipschitzWith ((1 / 4) ^ L) sigmoid^[L] :=
  lipschitzWith_sigmoid.iterate L

/-- A leaky ReLU: the input where it is positive, and a share `leak` of it where it is not.
Python: `max(x, leak * x)`. -/
def APPLY_LEAKY_RELU (leak x : ℝ) : ℝ :=
  max x (leak * x)

variable {leak : ℝ}

/-- A leaky ReLU is no steeper than one. -/
theorem leakyRelu_sub_le (h1 : leak ≤ 1) {x y : ℝ} (hxy : x ≤ y) :
    APPLY_LEAKY_RELU leak y - APPLY_LEAKY_RELU leak x ≤ y - x := by
  simp only [APPLY_LEAKY_RELU, max_def]
  split_ifs <;> nlinarith

/-- **A leaky ReLU keeps a slope of at least its leak.** -/
theorem le_leakyRelu_sub (h1 : leak ≤ 1) {x y : ℝ} (hxy : x ≤ y) :
    leak * (y - x) ≤ APPLY_LEAKY_RELU leak y - APPLY_LEAKY_RELU leak x := by
  simp only [APPLY_LEAKY_RELU, max_def]
  split_ifs <;> nlinarith

/-- With a positive leak it is always rising: it merges no two inputs and is never dead. -/
theorem strictMono_leakyRelu (h0 : 0 < leak) (h1 : leak ≤ 1) :
    StrictMono (APPLY_LEAKY_RELU leak) := by
  intro x y hxy
  have h := le_leakyRelu_sub h1 hxy.le
  have hpos : 0 < leak * (y - x) := mul_pos h0 (sub_pos.mpr hxy)
  linarith

/-- **Pooling never steepens.** The higher of two lines is no steeper than the steeper of
them. -/
theorem lipschitzWith_max {X : Type*} [PseudoEMetricSpace X] {K : ℝ≥0} {f g : X → ℝ}
    (hf : LipschitzWith K f) (hg : LipschitzWith K g) :
    LipschitzWith K fun x => max (f x) (g x) := by
  have h := hf.max hg
  rwa [max_self] at h

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Spectral normalisation: a layer divided by its own size.
Python: `W / norm(W)`. -/
noncomputable def NORMALIZE_SPECTRALLY (W : E →L[ℝ] F) : E →L[ℝ] F :=
  ‖W‖⁻¹ • W

/-- After spectral normalisation a layer has size at most one. -/
theorem norm_spectralNormalize_le (W : E →L[ℝ] F) : ‖NORMALIZE_SPECTRALLY W‖ ≤ 1 := by
  rw [NORMALIZE_SPECTRALLY, norm_smul, norm_inv, norm_norm]
  rcases eq_or_ne ‖W‖ 0 with h | h
  · rw [h]; simp
  · rw [inv_mul_cancel₀ h]

/-- For a layer that is not zero, the size is exactly one. -/
theorem norm_spectralNormalize {W : E →L[ℝ] F} (hW : W ≠ 0) : ‖NORMALIZE_SPECTRALLY W‖ = 1 := by
  rw [NORMALIZE_SPECTRALLY, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hW)]

/-- **A spectrally normalised layer has slope at most one.** -/
theorem lipschitzWith_spectralNormalize (W : E →L[ℝ] F) :
    LipschitzWith 1 (NORMALIZE_SPECTRALLY W) := by
  refine (NORMALIZE_SPECTRALLY W).lipschitzWith.weaken ?_
  rw [← NNReal.coe_le_coe]
  exact norm_spectralNormalize_le W

end SquigglyLine
