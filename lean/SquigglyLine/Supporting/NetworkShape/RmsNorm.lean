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

Definitions: `GET_ROOT_MEAN_SQUARE`, `NORMALIZE_BY_RMS`,
`APPLY_PRE_NORM_BLOCK`, `APPLY_POST_NORM_BLOCK`.

Theorems:

* `rootMeanSquare_eq`            it is the root of the mean of the squares;
* `rootMeanSquare_smul`          scaling a vector scales its root mean square;
* `normalizeByRms_smul`          RMSNorm forgets the scale;
* `rootMeanSquare_normalizeByRms`  after RMSNorm the root mean square is one;
* `isScaleInvariant_comp_normalizeByRms`  any loss read through an RMSNorm is
                                 scale invariant;
* `inner_gradient_self_eq_zero_of_rmsNorm`  so its gradient is at right angles
                                 to the weights;
* `preNormBlock_smul`            pre-norm leaves the skip path alone;
* `preNormBlock_sub_smul`        what a pre-norm branch adds does not depend on
                                 the size of the stream;
* `rootMeanSquare_postNormBlock` post-norm resets the size.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import SquigglyLine.Supporting.Training.Symmetry

namespace SquigglyLine

open Real

/-- A vector with one real entry for each of the `Entries`.
Python: `list[float]`. -/
abbrev EntryVector (Entries : Type*) := EuclideanSpace ℝ Entries

/-- A branch of a block: it reads a vector and returns a vector of the same
size.
Python: `Callable[[list[float]], list[float]]`. -/
abbrev NormBranch (Entries : Type*) :=
  EntryVector Entries → EntryVector Entries

variable {Entries : Type*} [Fintype Entries]

/-- The root mean square of a vector: its length over the root of its number
of entries.
Python: `sqrt(mean(vector ** 2))`. -/
noncomputable def GET_ROOT_MEAN_SQUARE
    (vector : EntryVector Entries) : ℝ :=
  ‖vector‖ / √(Fintype.card Entries)

/-- It is the root of the mean of the squares. -/
theorem rootMeanSquare_eq
    (vector : EntryVector Entries) :
    let root_mean_square := GET_ROOT_MEAN_SQUARE vector
    let root_of_mean     := √((∑ i, vector i ^ 2) / Fintype.card Entries)
    root_mean_square = root_of_mean := by
  unfold_named_pieces
  rw [GET_ROOT_MEAN_SQUARE, EuclideanSpace.norm_eq,
    Real.sqrt_div' _ (Nat.cast_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

/-- Scaling a vector scales its root mean square. -/
theorem rootMeanSquare_smul
    {scale : ℝ}
    (scale_nonneg : 0 ≤ scale)
    (vector : EntryVector Entries) :
    let scaled_rms   := GET_ROOT_MEAN_SQUARE (scale • vector)
    let expected_rms := scale * GET_ROOT_MEAN_SQUARE vector
    scaled_rms = expected_rms := by
  unfold_named_pieces
  rw [GET_ROOT_MEAN_SQUARE, GET_ROOT_MEAN_SQUARE, norm_smul,
    Real.norm_of_nonneg scale_nonneg, mul_div_assoc]

/-- RMSNorm: a vector divided by its root mean square.
Python: `vector / sqrt(mean(vector ** 2))`. -/
noncomputable def NORMALIZE_BY_RMS
    (vector : EntryVector Entries) : EntryVector Entries :=
  (GET_ROOT_MEAN_SQUARE vector)⁻¹ • vector

/-- **RMSNorm forgets the scale.** -/
theorem normalizeByRms_smul
    {scale : ℝ}
    (scale_pos : 0 < scale)
    (vector : EntryVector Entries) :
    let normalised_scaled := NORMALIZE_BY_RMS (scale • vector)
    let normalised        := NORMALIZE_BY_RMS vector
    normalised_scaled = normalised := by
  unfold_named_pieces
  have scaled_rms :
      GET_ROOT_MEAN_SQUARE (scale • vector)
        = scale * GET_ROOT_MEAN_SQUARE vector :=
    rootMeanSquare_smul scale_pos.le vector
  rw [NORMALIZE_BY_RMS, NORMALIZE_BY_RMS, scaled_rms, smul_smul]
  congr 1
  rw [mul_inv, mul_comm scale⁻¹, mul_assoc, inv_mul_cancel₀ scale_pos.ne',
    mul_one]

/-- After RMSNorm the root mean square is one. -/
theorem rootMeanSquare_normalizeByRms
    [Nonempty Entries]
    {vector : EntryVector Entries}
    (vector_ne_zero : vector ≠ 0) :
    let normalised_rms := GET_ROOT_MEAN_SQUARE (NORMALIZE_BY_RMS vector)
    normalised_rms = 1 := by
  unfold_named_pieces
  have entry_count_pos : (0 : ℝ) < Fintype.card Entries := by
    exact_mod_cast Fintype.card_pos
  have rms_pos : 0 < GET_ROOT_MEAN_SQUARE vector :=
    div_pos (norm_pos_iff.mpr vector_ne_zero)
      (Real.sqrt_pos.mpr entry_count_pos)
  have scaled_rms :
      GET_ROOT_MEAN_SQUARE ((GET_ROOT_MEAN_SQUARE vector)⁻¹ • vector)
        = (GET_ROOT_MEAN_SQUARE vector)⁻¹ * GET_ROOT_MEAN_SQUARE vector :=
    rootMeanSquare_smul (inv_nonneg.mpr rms_pos.le) vector
  rw [NORMALIZE_BY_RMS, scaled_rms, inv_mul_cancel₀ rms_pos.ne']

/-- **Any loss read through an RMSNorm is scale invariant.** -/
theorem isScaleInvariant_comp_normalizeByRms
    (loss : EntryVector Entries → ℝ) :
    let loss_through_norm : EntryVector Entries → ℝ :=
      fun weights => loss (NORMALIZE_BY_RMS weights)
    IS_SCALE_INVARIANT loss_through_norm := by
  unfold_named_pieces
  intro scale scale_pos weights
  show loss (NORMALIZE_BY_RMS (scale • weights))
    = loss (NORMALIZE_BY_RMS weights)
  have same_normalised :
      NORMALIZE_BY_RMS (scale • weights) = NORMALIZE_BY_RMS weights :=
    normalizeByRms_smul scale_pos weights
  rw [same_normalised]

/-- **So its gradient is at right angles to the weights.** -/
theorem inner_gradient_self_eq_zero_of_rmsNorm
    (loss : EntryVector Entries → ℝ)
    {weights gradient : EntryVector Entries}
    (gradient_gives_the_rate :
      HasDerivAt
        (fun stretch : ℝ =>
          loss (NORMALIZE_BY_RMS (weights + stretch • weights)))
        (inner ℝ gradient weights) 0) :
    let rate_along_the_weights := inner ℝ gradient weights
    rate_along_the_weights = 0 := by
  unfold_named_pieces
  exact inner_gradient_self_eq_zero
    (isScaleInvariant_comp_normalizeByRms loss) gradient_gives_the_rate

/-- A pre-norm block: the branch reads the normalised stream, and its output is
added to the stream as it was.
Python: `stream + branch(NORMALIZE_BY_RMS(stream))`. -/
noncomputable def APPLY_PRE_NORM_BLOCK
    (branch : NormBranch Entries)
    (stream : EntryVector Entries) : EntryVector Entries :=
  stream + branch (NORMALIZE_BY_RMS stream)

/-- A post-norm block: the branch reads the stream, and the sum is normalised.
Python: `NORMALIZE_BY_RMS(stream + branch(stream))`. -/
noncomputable def APPLY_POST_NORM_BLOCK
    (branch : NormBranch Entries)
    (stream : EntryVector Entries) : EntryVector Entries :=
  NORMALIZE_BY_RMS (stream + branch stream)

/-- **Pre-norm leaves the skip path alone.** Scale the stream and the skip path
carries the scale through, while the branch adds what it added before. -/
theorem preNormBlock_smul
    (branch : NormBranch Entries)
    {scale : ℝ}
    (scale_pos : 0 < scale)
    (stream : EntryVector Entries) :
    let scaled_block   := APPLY_PRE_NORM_BLOCK branch (scale • stream)
    let carried_scale  := scale • stream + branch (NORMALIZE_BY_RMS stream)
    scaled_block = carried_scale := by
  unfold_named_pieces
  have same_normalised :
      NORMALIZE_BY_RMS (scale • stream) = NORMALIZE_BY_RMS stream :=
    normalizeByRms_smul scale_pos stream
  rw [APPLY_PRE_NORM_BLOCK, same_normalised]

/-- What a pre-norm branch adds does not depend on the size of the stream. -/
theorem preNormBlock_sub_smul
    (branch : NormBranch Entries)
    {scale : ℝ}
    (scale_pos : 0 < scale)
    (stream : EntryVector Entries) :
    let added_to_scaled := APPLY_PRE_NORM_BLOCK branch (scale • stream)
      - scale • stream
    let added           := APPLY_PRE_NORM_BLOCK branch stream - stream
    added_to_scaled = added := by
  unfold_named_pieces
  have scaled_block :
      APPLY_PRE_NORM_BLOCK branch (scale • stream)
        = scale • stream + branch (NORMALIZE_BY_RMS stream) :=
    preNormBlock_smul branch scale_pos stream
  rw [scaled_block, APPLY_PRE_NORM_BLOCK, add_sub_cancel_left,
    add_sub_cancel_left]

/-- **Post-norm resets the size.** Its output always has root mean square
one. -/
theorem rootMeanSquare_postNormBlock
    [Nonempty Entries]
    (branch : NormBranch Entries)
    {stream : EntryVector Entries}
    (sum_ne_zero : stream + branch stream ≠ 0) :
    let block_rms := GET_ROOT_MEAN_SQUARE (APPLY_POST_NORM_BLOCK branch stream)
    block_rms = 1 := by
  unfold_named_pieces
  exact rootMeanSquare_normalizeByRms sum_ne_zero

end SquigglyLine
