/-
Skip connections and normalisation, as polarizers.

A `plate e` keeps the shadow of the light on the axis `e`. Light here lives in
any real inner product space, so the statements hold for any width.

A skip connection is a plate with a bypass, `skipPlate e v = v + plate e v`:
* `norm_le_norm_skipPlate` : it never dims the light.
* `skipPlate_of_crossed` : a crossed plate with a bypass does nothing, where a
  bare crossed plate blocks (`plate_of_crossed`).
* `inner_skipPlate`, `skipPlate_sub_plate` : it doubles the part along the
  axis and leaves the rest. The light turns part of the way.
* `inner_iterate_skipPlate`, `iterate_skipPlate_sub_plate` : `k` of them
  bring the light ever closer to the axis and never onto it.

Normalisation is an amplifier, `renorm v = ‖v‖⁻¹ • v`:
* `renorm_plate` : after a plate and an amplifier the light lies along the
  axis at full strength, for any turn short of a right angle.
* `throughNormedPlates_eq` : so a whole stack of plates with amplifiers
  delivers full strength along the last axis.
* `renorm_plate_of_crossed` : it cannot revive light that a crossed plate
  blocked.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Module

namespace SquigglyLine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {e v : E}

/-! ### A plate -/

/-- A polarizer plate with axis `e`: the shadow of `v` on `e`. -/
noncomputable def plate (e v : E) : E :=
  inner ℝ e v • e

/-- **Malus's law.** The shadow is as long as the overlap with the axis. -/
theorem norm_plate (he : ‖e‖ = 1) (v : E) : ‖plate e v‖ = |inner ℝ e v| := by
  rw [plate, norm_smul, he, mul_one, Real.norm_eq_abs]

/-- **Crossed plates block.** -/
theorem plate_of_crossed (h : inner ℝ e v = 0) : plate e v = 0 := by
  rw [plate, h, zero_smul]

/-! ### A skip connection: a plate with a bypass -/

/-- A plate with a bypass: the light that went around is added to the light that went
through. -/
noncomputable def skipPlate (e v : E) : E :=
  v + plate e v

/-- **A crossed plate with a bypass does nothing.** -/
theorem skipPlate_of_crossed (h : inner ℝ e v = 0) : skipPlate e v = v := by
  rw [skipPlate, plate_of_crossed h, add_zero]

/-- The squared length after a plate with a bypass. -/
theorem norm_skipPlate_sq (he : ‖e‖ = 1) (v : E) :
    ‖skipPlate e v‖ ^ 2 = ‖v‖ ^ 2 + 3 * inner ℝ e v ^ 2 := by
  have hcomm : inner ℝ v e = inner ℝ e v := real_inner_comm _ _
  rw [skipPlate, plate, norm_add_sq_real, real_inner_smul_right, hcomm, norm_smul, mul_pow, he,
    Real.norm_eq_abs, sq_abs]
  ring

/-- **A plate with a bypass never dims the light.** -/
theorem norm_le_norm_skipPlate (he : ‖e‖ = 1) (v : E) : ‖v‖ ≤ ‖skipPlate e v‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [norm_skipPlate_sq he]
  nlinarith [sq_nonneg (inner ℝ e v)]

/-- **The part along the axis doubles.** -/
theorem inner_skipPlate (he : ‖e‖ = 1) (v : E) :
    inner ℝ e (skipPlate e v) = 2 * inner ℝ e v := by
  rw [skipPlate, plate, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, he]
  ring

/-- **The rest is left as it was.** -/
theorem skipPlate_sub_plate (he : ‖e‖ = 1) (v : E) :
    skipPlate e v - plate e (skipPlate e v) = v - plate e v := by
  rw [plate, inner_skipPlate he, skipPlate, plate]
  module

/-- After `k` plates with a bypass on the same axis, the part along the axis has grown
`2 ^ k` times. -/
theorem inner_iterate_skipPlate (he : ‖e‖ = 1) (v : E) (k : ℕ) :
    inner ℝ e ((skipPlate e)^[k] v) = 2 ^ k * inner ℝ e v := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', inner_skipPlate he, ih, pow_succ]
    ring

/-- **Closer at every plate, never there.** After `k` plates with a bypass the part of the
light off the axis is exactly what it was. -/
theorem iterate_skipPlate_sub_plate (he : ‖e‖ = 1) (v : E) (k : ℕ) :
    (skipPlate e)^[k] v - plate e ((skipPlate e)^[k] v) = v - plate e v := by
  induction k with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', skipPlate_sub_plate he, ih]

/-! ### Normalisation: an amplifier -/

/-- An amplifier that brings the light back to full strength. -/
noncomputable def renorm (v : E) : E :=
  ‖v‖⁻¹ • v

/-- **Full strength.** -/
theorem norm_renorm (hv : v ≠ 0) : ‖renorm v‖ = 1 := by
  rw [renorm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

/-- **Nothing in, nothing out.** -/
theorem renorm_zero : renorm (0 : E) = 0 := by
  rw [renorm, smul_zero]

/-- **A plate and an amplifier turn the light without loss.** For any turn short of a right
angle, the light comes out along the axis at full strength. -/
theorem renorm_plate (he : ‖e‖ = 1) (h : 0 < inner ℝ e v) : renorm (plate e v) = e := by
  rw [renorm, norm_plate he, abs_of_pos h, plate, inv_smul_smul₀ h.ne']

/-- With any overlap at all, of either sign, the output has full strength. -/
theorem norm_renorm_plate (he : ‖e‖ = 1) (h : inner ℝ e v ≠ 0) : ‖renorm (plate e v)‖ = 1 := by
  refine norm_renorm ?_
  have hpos : 0 < ‖plate e v‖ := by
    rw [norm_plate he]
    exact abs_pos.mpr h
  exact norm_pos_iff.mp hpos

/-- **An amplifier cannot raise the dead.** After a crossed plate there is nothing to
amplify. -/
theorem renorm_plate_of_crossed (h : inner ℝ e v = 0) : renorm (plate e v) = 0 := by
  rw [plate_of_crossed h, renorm_zero]

/-- A stack of plates with axes `axis 1, axis 2, …`, an amplifier after each, lit by
full-strength light along `axis 0`. -/
noncomputable def throughNormedPlates (axis : ℕ → E) : ℕ → E
  | 0 => axis 0
  | k + 1 => renorm (plate (axis (k + 1)) (throughNormedPlates axis k))

/-- **With amplifiers the loss is gone.** If each plate is turned less than a right angle
from the last, the light comes out along the last axis at full strength, whatever the sizes
of the turns. -/
theorem throughNormedPlates_eq {axis : ℕ → E} (hunit : ∀ k, ‖axis k‖ = 1)
    (hturn : ∀ k, 0 < inner ℝ (axis (k + 1)) (axis k)) (k : ℕ) :
    throughNormedPlates axis k = axis k := by
  induction k with
  | zero => rfl
  | succ n ih => rw [throughNormedPlates, ih, renorm_plate (hunit _) (hturn n)]

end SquigglyLine
