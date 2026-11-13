/-
RMSNorm and pre-norm.

RMSNorm divides a vector by its root mean square. That alone makes whatever
comes before it free to rescale: multiply the vector by any positive number
and the output is the same. So a loss read through an RMSNorm is scale
invariant, and by `Symmetry.lean` its gradient is at right angles to the
weights. No mean has to be subtracted for this.

A pre-norm block normalises inside the branch and leaves the skip path
alone, so what the branch adds does not depend on how large the stream is. A
post-norm block normalises the sum, so its output always has root mean
square one.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Definitions: `GET_ROOT_MEAN_SQUARE`, `NORMALIZE_BY_RMS`,
`APPLY_PRE_NORM_BLOCK`, `APPLY_POST_NORM_BLOCK`.

Theorems: `rootMeanSquare_eq`, `rootMeanSquare_smul`, `normalizeByRms_smul`,
`rootMeanSquare_normalizeByRms`, `isScaleInvariant_comp_normalizeByRms`,
`inner_gradient_self_eq_zero_of_rmsNorm`, `preNormBlock_smul`,
`preNormBlock_sub_smul`, `rootMeanSquare_postNormBlock`.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import SquigglyLine.Supporting.Training.Symmetry

namespace SquigglyLine

open Real

variable {ι : Type*} [Fintype ι]

/-- The root mean square of a vector: its length over the root of its number of entries.
Python: `sqrt(mean(v ** 2))`. -/
noncomputable def GET_ROOT_MEAN_SQUARE (v : EuclideanSpace ℝ ι) : ℝ :=
  ‖v‖ / √(Fintype.card ι)

/-- It is the root of the mean of the squares. -/
theorem rootMeanSquare_eq (v : EuclideanSpace ℝ ι) :
    GET_ROOT_MEAN_SQUARE v = √((∑ i, v i ^ 2) / Fintype.card ι) := by
  rw [GET_ROOT_MEAN_SQUARE, EuclideanSpace.norm_eq, Real.sqrt_div' _ (Nat.cast_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

/-- Scaling a vector scales its root mean square. -/
theorem rootMeanSquare_smul {c : ℝ} (hc : 0 ≤ c) (v : EuclideanSpace ℝ ι) :
    GET_ROOT_MEAN_SQUARE (c • v) = c * GET_ROOT_MEAN_SQUARE v := by
  rw [GET_ROOT_MEAN_SQUARE, GET_ROOT_MEAN_SQUARE, norm_smul, Real.norm_of_nonneg hc,
    mul_div_assoc]

/-- RMSNorm: a vector divided by its root mean square.
Python: `v / sqrt(mean(v ** 2))`. -/
noncomputable def NORMALIZE_BY_RMS (v : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  (GET_ROOT_MEAN_SQUARE v)⁻¹ • v

/-- **RMSNorm forgets the scale.** -/
theorem normalizeByRms_smul {c : ℝ} (hc : 0 < c) (v : EuclideanSpace ℝ ι) :
    NORMALIZE_BY_RMS (c • v) = NORMALIZE_BY_RMS v := by
  rw [NORMALIZE_BY_RMS, NORMALIZE_BY_RMS, rootMeanSquare_smul hc.le, smul_smul]
  congr 1
  rw [mul_inv, mul_comm c⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

/-- After RMSNorm the root mean square is one. -/
theorem rootMeanSquare_normalizeByRms [Nonempty ι] {v : EuclideanSpace ℝ ι} (hv : v ≠ 0) :
    GET_ROOT_MEAN_SQUARE (NORMALIZE_BY_RMS v) = 1 := by
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hr : 0 < GET_ROOT_MEAN_SQUARE v :=
    div_pos (norm_pos_iff.mpr hv) (Real.sqrt_pos.mpr hcard)
  rw [NORMALIZE_BY_RMS, rootMeanSquare_smul (inv_nonneg.mpr hr.le), inv_mul_cancel₀ hr.ne']

/-- **Any loss read through an RMSNorm is scale invariant.** -/
theorem isScaleInvariant_comp_normalizeByRms (loss : EuclideanSpace ℝ ι → ℝ) :
    IS_SCALE_INVARIANT fun w => loss (NORMALIZE_BY_RMS w) := by
  intro c hc w
  show loss (NORMALIZE_BY_RMS (c • w)) = loss (NORMALIZE_BY_RMS w)
  rw [normalizeByRms_smul hc]

/-- **So its gradient is at right angles to the weights.** -/
theorem inner_gradient_self_eq_zero_of_rmsNorm (loss : EuclideanSpace ℝ ι → ℝ)
    {w g : EuclideanSpace ℝ ι}
    (h : HasDerivAt (fun s : ℝ => loss (NORMALIZE_BY_RMS (w + s • w))) (inner ℝ g w) 0) :
    inner ℝ g w = 0 :=
  inner_gradient_self_eq_zero (isScaleInvariant_comp_normalizeByRms loss) h

/-- A pre-norm block: the branch reads the normalised stream, and its output is added to the
stream as it was.
Python: `x + branch(NORMALIZE_BY_RMS(x))`. -/
noncomputable def APPLY_PRE_NORM_BLOCK (branch : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  x + branch (NORMALIZE_BY_RMS x)

/-- A post-norm block: the branch reads the stream, and the sum is normalised.
Python: `NORMALIZE_BY_RMS(x + branch(x))`. -/
noncomputable def APPLY_POST_NORM_BLOCK (branch : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  NORMALIZE_BY_RMS (x + branch x)

/-- **Pre-norm leaves the skip path alone.** Scale the stream and the skip path carries the
scale through, while the branch adds what it added before. -/
theorem preNormBlock_smul (branch : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) {c : ℝ}
    (hc : 0 < c) (x : EuclideanSpace ℝ ι) :
    APPLY_PRE_NORM_BLOCK branch (c • x) = c • x + branch (NORMALIZE_BY_RMS x) := by
  rw [APPLY_PRE_NORM_BLOCK, normalizeByRms_smul hc]

/-- What a pre-norm branch adds does not depend on the size of the stream. -/
theorem preNormBlock_sub_smul (branch : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) {c : ℝ}
    (hc : 0 < c) (x : EuclideanSpace ℝ ι) :
    APPLY_PRE_NORM_BLOCK branch (c • x) - c • x = APPLY_PRE_NORM_BLOCK branch x - x := by
  rw [preNormBlock_smul branch hc, APPLY_PRE_NORM_BLOCK, add_sub_cancel_left,
    add_sub_cancel_left]

/-- **Post-norm resets the size.** Its output always has root mean square one. -/
theorem rootMeanSquare_postNormBlock [Nonempty ι]
    (branch : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) {x : EuclideanSpace ℝ ι}
    (h : x + branch x ≠ 0) :
    GET_ROOT_MEAN_SQUARE (APPLY_POST_NORM_BLOCK branch x) = 1 :=
  rootMeanSquare_normalizeByRms h

end SquigglyLine
