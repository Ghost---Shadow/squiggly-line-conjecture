/-
Flat minima: flatter is farther.

Rescale a model: multiply its parameters by `c`, and divide them by `c` before
use. Nothing it computes changes.

* `rescale_smul`, `residual_rescale` : same outputs, same error.
* `norm_rescale_sq`, `kernel_rescale` : the loss is flatter by `c²`.
* `travel_rescale` : the nearest fit is farther by `|c|`.
* `gradientStep_rescale` : a gradient step of the rescaled model is a step of
  the old one with step size `η / c²`.
* `strength_mul_travel_sq` : what does not change. Along a direction of
  strength `lam`, strength times travel squared is the error squared.
-/
import SquigglyLine.DoubleDescent

namespace SquigglyLine

open scoped Pointwise

/-! ### The same model in other units -/

section Units

variable {Θ Y : Type*}
  [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The model `A` with its parameters measured in units `c` times smaller: the new
parameters are `c` times the old ones, and are divided by `c` before use. -/
noncomputable def rescale (c : ℝ) (A : Θ →L[ℝ] Y) : Θ →L[ℝ] Y :=
  c⁻¹ • A

/-- **Same outputs.** The rescaled model at `c • θ` gives what the model gave at `θ`. -/
theorem rescale_smul {c : ℝ} (hc : c ≠ 0) (A : Θ →L[ℝ] Y) (θ : Θ) :
    rescale c A (c • θ) = A θ := by
  rw [rescale, smul_apply, map_smul, inv_smul_smul₀ hc]

/-- **Same error.** -/
theorem residual_rescale {c : ℝ} (hc : c ≠ 0) (A : Θ →L[ℝ] Y) (y : Y) (θ : Θ) :
    residual (rescale c A : Θ →ₗ[ℝ] Y) y (c • θ) = residual (A : Θ →ₗ[ℝ] Y) y θ := by
  simp only [residual, ContinuousLinearMap.coe_coe, rescale_smul hc]

/-- **Flatter by `c²`.** The curvature of the loss along any direction is divided by `c²`. -/
theorem norm_rescale_sq (c : ℝ) (A : Θ →L[ℝ] Y) (δ : Θ) :
    ‖rescale c A δ‖ ^ 2 = ‖A δ‖ ^ 2 / c ^ 2 := by
  rw [rescale, smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    inv_pow]
  ring

/-- The distances to the fits are all multiplied by `|c|`. -/
theorem fitDistances_rescale {c : ℝ} (hc : c ≠ 0) (A : Θ →L[ℝ] Y) (y : Y) (θ₀ : Θ) :
    fitDistances (rescale c A : Θ →ₗ[ℝ] Y) y (c • θ₀)
      = |c| • fitDistances (A : Θ →ₗ[ℝ] Y) y θ₀ := by
  ext d
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨θ', hθ', rfl⟩
    refine ⟨‖c⁻¹ • θ' - θ₀‖, ⟨c⁻¹ • θ', ?_, rfl⟩, ?_⟩
    · have h : rescale c A θ' = y := hθ'
      rw [← h, rescale, smul_apply, ContinuousLinearMap.coe_coe, map_smul]
    · have hsub : c⁻¹ • θ' - θ₀ = c⁻¹ • (θ' - c • θ₀) := by rw [smul_sub, inv_smul_smul₀ hc]
      rw [hsub, norm_smul, norm_inv, Real.norm_eq_abs, smul_eq_mul,
        mul_inv_cancel_left₀ (abs_ne_zero.mpr hc)]
  · rintro ⟨_, ⟨θ, hθ, rfl⟩, rfl⟩
    refine ⟨c • θ, ?_, ?_⟩
    · have h : A θ = y := hθ
      rw [ContinuousLinearMap.coe_coe, rescale_smul hc, h]
    · rw [← smul_sub, norm_smul, Real.norm_eq_abs, smul_eq_mul]

/-- **Farther by `|c|`.** The nearest fit of the rescaled model is `|c|` times as far from
the start. -/
theorem travel_rescale {c : ℝ} (hc : c ≠ 0) (A : Θ →L[ℝ] Y) (y : Y) (θ₀ : Θ) :
    travel (rescale c A : Θ →ₗ[ℝ] Y) y (c • θ₀) = |c| * travel (A : Θ →ₗ[ℝ] Y) y θ₀ := by
  rw [travel, travel, fitDistances_rescale hc, Real.sInf_smul_of_nonneg (abs_nonneg c),
    smul_eq_mul]

/-- **Flatter is farther.** Rescaling by `c` keeps the error, divides the curvature of the
loss by `c²`, and multiplies the distance to the nearest fit by `|c|`. -/
theorem flatter_is_farther {c : ℝ} (hc : c ≠ 0) (A : Θ →L[ℝ] Y) (y : Y) (θ₀ : Θ) :
    residual (rescale c A : Θ →ₗ[ℝ] Y) y (c • θ₀) = residual (A : Θ →ₗ[ℝ] Y) y θ₀
      ∧ (∀ δ, ‖rescale c A δ‖ ^ 2 = ‖A δ‖ ^ 2 / c ^ 2)
      ∧ travel (rescale c A : Θ →ₗ[ℝ] Y) y (c • θ₀) = |c| * travel (A : Θ →ₗ[ℝ] Y) y θ₀ :=
  ⟨residual_rescale hc A y θ₀, norm_rescale_sq c A, travel_rescale hc A y θ₀⟩

end Units

/-! ### The kernel, the gradient step, and what does not change -/

section Training

open ContinuousLinearMap

variable {Θ Y : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The adjoint of the rescaled model. -/
theorem adjoint_rescale (c : ℝ) (A : Θ →L[ℝ] Y) : adjoint (rescale c A) = c⁻¹ • adjoint A := by
  rw [rescale, map_smulₛₗ, conj_trivial]

/-- **The kernel is weaker by `c²`.** -/
theorem kernel_rescale (c : ℝ) (A : Θ →L[ℝ] Y) (v : Y) :
    rescale c A (adjoint (rescale c A) v) = (c ^ 2)⁻¹ • A (adjoint A v) := by
  rw [adjoint_rescale, rescale, smul_apply, smul_apply, map_smul, smul_smul, ← mul_inv, ← sq]

/-- **Rescaling is a change of step size.** A gradient step of the rescaled model with step
size `η` is a step of the model with step size `η / c²`. -/
theorem gradientStep_rescale {c : ℝ} (hc : c ≠ 0) (A : Θ →L[ℝ] Y) (y : Y) (η : ℝ) (θ : Θ) :
    gradientStep (rescale c A) y η (c • θ) = c • gradientStep A y (η / c ^ 2) θ := by
  have hstep : η * c⁻¹ = c * (η / c ^ 2) := by field_simp
  rw [gradientStep, gradientStep, residual_rescale hc, adjoint_rescale, smul_apply, smul_add,
    smul_smul, smul_smul, hstep]

/-- **What does not change.** If the residual lies along a direction of strength `lam`, then
strength times travel squared is the error squared. Flat means far and sharp means near. -/
theorem strength_mul_travel_sq (A : Θ →L[ℝ] Y) (Kinv : Y → Y)
    (hinv : ∀ v, A (adjoint A (Kinv v)) = v) {lam : ℝ} (hlam : 0 < lam) (y : Y) (θ₀ : Θ)
    (heig : A (adjoint A (residual (A : Θ →ₗ[ℝ] Y) y θ₀))
      = lam • residual (A : Θ →ₗ[ℝ] Y) y θ₀) :
    lam * travel (A : Θ →ₗ[ℝ] Y) y θ₀ ^ 2 = ‖residual (A : Θ →ₗ[ℝ] Y) y θ₀‖ ^ 2 := by
  rw [travel_eq_of_eigen A Kinv hinv hlam y θ₀ heig, div_pow, Real.sq_sqrt hlam.le]
  field_simp

end Training

end SquigglyLine
