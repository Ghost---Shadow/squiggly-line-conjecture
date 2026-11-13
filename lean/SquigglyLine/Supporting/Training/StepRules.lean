/-
Rules for the step: Adam, clipping, a subspace, rounding.

Plain gradient descent takes a step in proportion to the gradient. These are
four other rules in common use, each read as a statement about travel.

Adam with no memory (`TAKE_ADAM_STEP`), one coordinate at a time:
* `adamStep_eq_sign` : the step is the sign of the gradient.
* `adamStep_mul` : multiplying the loss by a positive number changes nothing.
* `abs_adamStep` : every coordinate with a gradient moves the same distance.
* `abs_sub_signStep` : so a gap `d` closes by exactly `η` per step, whatever
  the strength of the direction.

Gradient clipping (`CLIP`):
* `norm_clip_le` : a clipped gradient is no longer than the limit.
* `clip_of_norm_le` : a gradient within the limit is left alone.
* `norm_sum_clip_le` : so `t` steps travel at most `t η c`.

Training inside a subspace:
* `travel_le_travel_comp` : weights confined to a subspace never have a
  shorter trip to a fit.

Rounding the weights:
* `abs_liftedModel_add_sub_le` : moving the weights by `δ` moves each output
  by at most `‖δ‖` times the size of the features.
* `lipschitzWith_liftedModel_add_sub` : and changes the slope by at most `‖δ‖`
  times the stretch of the lift.
-/
import Mathlib.Analysis.Real.Sqrt
import SquigglyLine.Networks.Lift
import SquigglyLine.Networks.LinearModel

namespace SquigglyLine

open NNReal

/-! ### Adam with no memory -/

section Adam

/-- One coordinate of an Adam step with no memory of earlier steps: the gradient divided by
its own size. -/
noncomputable def TAKE_ADAM_STEP (g : ℝ) : ℝ :=
  g / √(g ^ 2)

/-- **The step is the sign of the gradient.** -/
theorem adamStep_eq_sign (g : ℝ) : TAKE_ADAM_STEP g = SignType.sign g := by
  rw [TAKE_ADAM_STEP, Real.sqrt_sq_eq_abs]
  rcases lt_trichotomy g 0 with h | rfl | h
  · rw [abs_of_neg h, sign_neg h, div_neg, div_self h.ne]
    simp
  · simp
  · rw [abs_of_pos h, sign_pos h, div_self h.ne']
    simp

/-- **Multiplying the loss by a positive number changes nothing.** -/
theorem adamStep_mul {c : ℝ} (hc : 0 < c) (g : ℝ) : TAKE_ADAM_STEP (c * g) = TAKE_ADAM_STEP g := by
  rw [adamStep_eq_sign, adamStep_eq_sign, sign_mul, sign_pos hc, one_mul]

/-- **Every coordinate with a gradient moves the same distance.** -/
theorem abs_adamStep {g : ℝ} (hg : g ≠ 0) : |TAKE_ADAM_STEP g| = 1 := by
  rw [TAKE_ADAM_STEP, Real.sqrt_sq_eq_abs, abs_div, abs_abs, div_self (abs_ne_zero.mpr hg)]

/-- **A gap closes by `η` per step, whatever the strength.** A coordinate is off by `d`. A
step of size `η` against the sign of the error leaves it off by `|d| - η`. The strength of the
direction does not appear. -/
theorem abs_sub_signStep {d η : ℝ} (hη : 0 ≤ η) (hle : η ≤ |d|) :
    |d - η * SignType.sign d| = |d| - η := by
  rcases lt_trichotomy d 0 with h | rfl | h
  · have hle' : η ≤ -d := by rwa [abs_of_neg h] at hle
    rw [sign_neg h, abs_of_neg h]
    simp only [SignType.coe_neg_one, mul_neg, mul_one, sub_neg_eq_add]
    rw [abs_of_nonpos (by linarith)]
    ring
  · have hzero : η = 0 := le_antisymm (by simpa using hle) hη
    simp [hzero]
  · have hle' : η ≤ d := by rwa [abs_of_pos h] at hle
    rw [sign_pos h, abs_of_pos h]
    simp only [SignType.coe_one, mul_one]
    rw [abs_of_nonneg (by linarith)]

end Adam

/-! ### Gradient clipping -/

section Clip

variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

/-- Clip a gradient to length at most `c`, keeping its direction. -/
noncomputable def CLIP (c : ℝ) (g : Θ) : Θ :=
  min 1 (c / ‖g‖) • g

/-- **A clipped gradient is no longer than the limit.** -/
theorem norm_clip_le {c : ℝ} (hc : 0 ≤ c) (g : Θ) : ‖CLIP c g‖ ≤ c := by
  rcases eq_or_ne g 0 with rfl | hg
  · simpa [CLIP] using hc
  have hpos : 0 < ‖g‖ := norm_pos_iff.mpr hg
  rw [CLIP, norm_smul, Real.norm_of_nonneg (le_min zero_le_one (div_nonneg hc hpos.le))]
  calc min 1 (c / ‖g‖) * ‖g‖ ≤ c / ‖g‖ * ‖g‖ :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hpos.le
    _ = c := div_mul_cancel₀ c hpos.ne'

/-- A gradient within the limit is left alone. -/
theorem clip_of_norm_le {c : ℝ} {g : Θ} (hg : g ≠ 0) (h : ‖g‖ ≤ c) : CLIP c g = g := by
  rw [CLIP, min_eq_left ((one_le_div (norm_pos_iff.mpr hg)).mpr h), one_smul]

/-- **Clipping caps the travel.** After `t` steps of size `η` with gradients clipped to `c`,
the weights have moved at most `t η c`, whatever the gradients were. -/
theorem norm_sum_clip_le {c : ℝ} (hc : 0 ≤ c) (g : ℕ → Θ) (η : ℝ) (t : ℕ) :
    ‖∑ k ∈ Finset.range t, η • CLIP c (g k)‖ ≤ t * (|η| * c) := by
  calc ‖∑ k ∈ Finset.range t, η • CLIP c (g k)‖
      ≤ ∑ k ∈ Finset.range t, ‖η • CLIP c (g k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range t, |η| * c := Finset.sum_le_sum fun k _ => by
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_clip_le hc _) (abs_nonneg _)
    _ = t * (|η| * c) := by simp

end Clip

/-! ### Training inside a subspace -/

section Subspace

variable {Θ Θ' Y : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup Θ'] [NormedSpace ℝ Θ']
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **Confining the weights never shortens the trip.** Let the weights move only inside a
subspace, given by a map `P` that keeps lengths. If a fit exists there, it is at least as far
from the start as the nearest fit of the full model. -/
theorem travel_le_travel_comp (A : Θ →ₗ[ℝ] Y) (P : Θ' →ₗ[ℝ] Θ) (hP : ∀ δ, ‖P δ‖ = ‖δ‖) (y : Y)
    (θ₀ : Θ') (hfit : ∃ θ, A (P θ) = y) :
    GET_TRAVEL A y (P θ₀) ≤ GET_TRAVEL (A ∘ₗ P) y θ₀ := by
  refine csInf_le_csInf ⟨0, ?_⟩ ?_ ?_
  · rintro d ⟨θ, -, rfl⟩
    exact norm_nonneg _
  · obtain ⟨θ, hθ⟩ := hfit
    exact ⟨_, θ, hθ, rfl⟩
  · rintro d ⟨θ, hθ, rfl⟩
    exact ⟨P θ, hθ, by rw [← map_sub, hP]⟩

end Subspace

/-! ### Rounding the weights -/

section Rounding

variable {X Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]

theorem liftedModel_add (φ : X → Θ) (θ δ : Θ) (x : X) :
    EVALUATE_LIFTED_MODEL φ (θ + δ) x = EVALUATE_LIFTED_MODEL φ θ x + EVALUATE_LIFTED_MODEL φ δ x :=
  inner_add_left _ _ _

/-- **Rounding moves each output by at most the rounding error times the size of the
features.** -/
theorem abs_liftedModel_add_sub_le (φ : X → Θ) (θ δ : Θ) (x : X) :
    |EVALUATE_LIFTED_MODEL φ (θ + δ) x - EVALUATE_LIFTED_MODEL φ θ x| ≤ ‖δ‖ * ‖φ x‖ := by
  rw [liftedModel_add, add_sub_cancel_left]
  exact abs_real_inner_le_norm _ _

/-- **Rounding changes the slope by at most the rounding error times the stretch of the
lift.** -/
theorem lipschitzWith_liftedModel_add_sub [PseudoMetricSpace X] {φ : X → Θ} {K : ℝ≥0}
    (hφ : LipschitzWith K φ) (θ δ : Θ) :
    LipschitzWith (‖δ‖₊ * K) fun x => EVALUATE_LIFTED_MODEL φ (θ + δ) x - EVALUATE_LIFTED_MODEL φ θ x := by
  simp only [liftedModel_add, add_sub_cancel_left]
  exact lipschitzWith_liftedModel hφ δ

end Rounding

end SquigglyLine
