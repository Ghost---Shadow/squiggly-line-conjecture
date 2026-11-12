/-
Weight decay, early stopping and spare parameters are one thing.

Follow a direction of the labels that the kernel stretches by `lam`. Weight
decay adds a penalty `mu` on the distance of the weights from their start.

* `residual_ridgeFit` : the weight-decay fit leaves the share `mu / (lam + mu)`
  of the error.
* `ridge_stationary`, `decayStep_ridgeFit` : it is where gradient descent
  with weight decay comes to rest.
* `inner_ridgeFit` : it moves the answer at a new input by the overlap divided
  by `lam + mu`. This is the benign-overfitting formula with `c' = mu`.
* `early_stopping_le_ridge` : stopping after `t` steps leaves at most
  `1 / (1 + t * x)` of the error, where `x = η * lam`.
* `ridge_share_eq` : and that is the share weight decay leaves when
  `mu = 1 / (η * t)`.
-/
import Mathlib.Tactic.LinearCombination
import SquigglyLine.Supporting.Training.SpectralBias

namespace SquigglyLine

/-! ### The share of the error left -/

section Share

/-- **Early stopping cuts at least as hard as weight decay.** After `t` steps at rate `x`
the share of the error left is at most `1 / (1 + t * x)`. -/
theorem early_stopping_le_ridge {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) (t : ℕ) :
    (1 - x) ^ t ≤ 1 / (1 + t * x) := by
  have hy : 0 ≤ (t : ℝ) * x := mul_nonneg (Nat.cast_nonneg t) h0
  calc (1 - x) ^ t ≤ Real.exp (-(t * x)) := pow_one_sub_le_exp h1 t
    _ = 1 / Real.exp (t * x) := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / (1 + t * x) :=
        one_div_le_one_div_of_le (by linarith) (by linarith [Real.add_one_le_exp ((t : ℝ) * x)])

/-- **The matching penalty.** Weight decay with `mu = 1 / (η * t)` leaves the share
`1 / (1 + t * (η * lam))`. -/
theorem ridge_share_eq {η lam : ℝ} {t : ℕ} (hη : 0 < η) (ht : 0 < t) (hlam : 0 ≤ lam) :
    1 / (η * t) / (lam + 1 / (η * t)) = 1 / (1 + t * (η * lam)) := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hηt : 0 < η * t := mul_pos hη ht'
  have hsum : 0 < lam + 1 / (η * t) := add_pos_of_nonneg_of_pos hlam (one_div_pos.mpr hηt)
  have hden : 0 < 1 + t * (η * lam) :=
    add_pos_of_pos_of_nonneg one_pos (mul_nonneg ht'.le (mul_nonneg hη.le hlam))
  rw [div_eq_div_iff hsum.ne' hden.ne']
  field_simp
  ring

end Share

/-! ### The fit that weight decay rests at -/

section Fit

open ContinuousLinearMap

variable {Θ Y : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The fit that weight decay with penalty `mu` rests at, when the error at the start lies
along a direction of strength `lam`. -/
noncomputable def ridgeFit (A : Θ →L[ℝ] Y) (y : Y) (θ₀ : Θ) (lam mu : ℝ) : Θ :=
  θ₀ + (lam + mu)⁻¹ • adjoint A (residual (A : Θ →ₗ[ℝ] Y) y θ₀)

/-- One step of gradient descent with weight decay `mu` towards the start `θ₀`. -/
noncomputable def decayStep (A : Θ →L[ℝ] Y) (y : Y) (η mu : ℝ) (θ₀ θ : Θ) : Θ :=
  gradientStep A y η θ - (η * mu) • (θ - θ₀)

variable (A : Θ →L[ℝ] Y) (y : Y) (θ₀ : Θ) {lam mu : ℝ}

/-- **What weight decay leaves.** The share `mu / (lam + mu)` of the error. -/
theorem residual_ridgeFit (hsum : lam + mu ≠ 0)
    (heig : A (adjoint A (residual (A : Θ →ₗ[ℝ] Y) y θ₀))
      = lam • residual (A : Θ →ₗ[ℝ] Y) y θ₀) :
    residual (A : Θ →ₗ[ℝ] Y) y (ridgeFit A y θ₀ lam mu)
      = (mu / (lam + mu)) • residual (A : Θ →ₗ[ℝ] Y) y θ₀ := by
  have hstep : residual (A : Θ →ₗ[ℝ] Y) y (ridgeFit A y θ₀ lam mu)
      = residual (A : Θ →ₗ[ℝ] Y) y θ₀
        - (lam + mu)⁻¹ • A (adjoint A (residual (A : Θ →ₗ[ℝ] Y) y θ₀)) := by
    simp only [residual, ridgeFit, ContinuousLinearMap.coe_coe, map_add, map_smul]
    abel
  have hone : (lam + mu)⁻¹ * (lam + mu) = 1 := inv_mul_cancel₀ hsum
  have hcoef : mu / (lam + mu) = 1 - (lam + mu)⁻¹ * lam := by
    rw [div_eq_inv_mul]
    linear_combination hone
  rw [hstep, heig, smul_smul, hcoef, sub_smul, one_smul]

/-- **The resting point.** At the weight-decay fit, the pull of the data and the pull of
the penalty balance. -/
theorem ridge_stationary (hsum : lam + mu ≠ 0)
    (heig : A (adjoint A (residual (A : Θ →ₗ[ℝ] Y) y θ₀))
      = lam • residual (A : Θ →ₗ[ℝ] Y) y θ₀) :
    adjoint A (residual (A : Θ →ₗ[ℝ] Y) y (ridgeFit A y θ₀ lam mu))
      = mu • (ridgeFit A y θ₀ lam mu - θ₀) := by
  rw [residual_ridgeFit A y θ₀ hsum heig, map_smul, ridgeFit, add_sub_cancel_left, smul_smul,
    div_eq_mul_inv]

/-- **Gradient descent with weight decay rests there.** -/
theorem decayStep_ridgeFit (η : ℝ) (hsum : lam + mu ≠ 0)
    (heig : A (adjoint A (residual (A : Θ →ₗ[ℝ] Y) y θ₀))
      = lam • residual (A : Θ →ₗ[ℝ] Y) y θ₀) :
    decayStep A y η mu θ₀ (ridgeFit A y θ₀ lam mu) = ridgeFit A y θ₀ lam mu := by
  rw [decayStep, gradientStep, ridge_stationary A y θ₀ hsum heig, smul_smul,
    add_sub_cancel_right]

/-- **Weight decay is spare parameters.** The answer at a new input with features `φ` moves
by the overlap divided by `lam + mu`. -/
theorem inner_ridgeFit (φ : Θ) (lam mu : ℝ) :
    inner ℝ φ (ridgeFit A y θ₀ lam mu)
      = inner ℝ φ θ₀ + inner ℝ (A φ) (residual (A : Θ →ₗ[ℝ] Y) y θ₀) / (lam + mu) := by
  rw [ridgeFit, inner_add_right, real_inner_smul_right, adjoint_inner_right]
  ring

end Fit

end SquigglyLine
