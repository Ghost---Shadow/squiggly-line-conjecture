/-
Spectral bias: strong directions are learned first.

Take a direction `u` of the labels that the kernel only stretches, by `lam`.

* `inner_residual_gradientStep` : one gradient step multiplies the error along
  `u` by `1 - η * lam`.
* `inner_residual_iterate_gradientStep` : after `t` steps the factor is
  `(1 - η * lam) ^ t`. Each direction shrinks on its own clock.
* `strong_directions_first` : a stronger direction has a smaller share left.
* `spectral_bias` : the share left after `t` steps lies between
  `1 - t * (η * lam)` and `exp (-(t * (η * lam)))`. The clock of a direction
  is `1 / (η * lam)` steps: it cannot be hurried, and it does run out.
* `inner_residual_iterate_of_kernel_eq_zero` : a direction of strength zero is
  never learned.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import SquigglyLine.Networks.DoubleDescent

namespace SquigglyLine

/-! ### The share of an error left after `t` steps -/

section Share

/-- A larger rate leaves a smaller share. -/
theorem pow_one_sub_anti {a b : ℝ} (hab : a ≤ b) (hb : b ≤ 1) (t : ℕ) :
    (1 - b) ^ t ≤ (1 - a) ^ t :=
  pow_le_pow_left₀ (by linarith) (by linarith) t

/-- **It cannot be hurried.** After `t` steps at rate `x`, at least `1 - t * x` is left. -/
theorem one_sub_mul_le_pow_one_sub {x : ℝ} (hx : x ≤ 1) (t : ℕ) : 1 - t * x ≤ (1 - x) ^ t := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -x by linarith) t
  calc 1 - t * x = 1 + t * -x := by ring
    _ ≤ (1 + -x) ^ t := h
    _ = (1 - x) ^ t := by rw [← sub_eq_add_neg]

/-- **It does run out.** After `t` steps at rate `x`, at most `exp (-(t * x))` is left. -/
theorem pow_one_sub_le_exp {x : ℝ} (hx : x ≤ 1) (t : ℕ) : (1 - x) ^ t ≤ Real.exp (-(t * x)) := by
  calc (1 - x) ^ t ≤ Real.exp (-x) ^ t :=
        pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg x) t
    _ = Real.exp (-(t * x)) := by rw [← Real.exp_nat_mul, mul_neg]

/-- **Strong directions are learned first.** With step size `η`, a direction of strength
`lam₂` has a smaller share of its error left than a weaker direction of strength `lam₁`. -/
theorem strong_directions_first {η lam₁ lam₂ : ℝ} (hη : 0 ≤ η) (hlam : lam₁ ≤ lam₂)
    (hle : η * lam₂ ≤ 1) (t : ℕ) : (1 - η * lam₂) ^ t ≤ (1 - η * lam₁) ^ t :=
  pow_one_sub_anti (mul_le_mul_of_nonneg_left hlam hη) hle t

end Share

/-! ### One direction of the kernel at a time -/

section Direction

open ContinuousLinearMap

variable {Θ Y : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- **One step, one direction.** If the kernel stretches `u` by `lam`, a gradient step
multiplies the error along `u` by `1 - η * lam`. -/
theorem inner_residual_gradientStep (A : Θ →L[ℝ] Y) (y : Y) (η : ℝ) (θ : Θ) {u : Y} {lam : ℝ}
    (hu : A (adjoint A u) = lam • u) :
    inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y (TAKE_GRADIENT_STEP A y η θ))
      = (1 - η * lam) * inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ) := by
  rw [residual_gradientStep, inner_sub_right, real_inner_smul_right, ← kernel_inner_comm, hu,
    real_inner_smul_left]
  ring

/-- **Each direction on its own clock.** After `t` steps the error along `u` is
`(1 - η * lam) ^ t` times what it was at the start. -/
theorem inner_residual_iterate_gradientStep (A : Θ →L[ℝ] Y) (y : Y) (η : ℝ) (θ₀ : Θ) {u : Y}
    {lam : ℝ} (hu : A (adjoint A u) = lam • u) (t : ℕ) :
    inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y ((TAKE_GRADIENT_STEP A y η)^[t] θ₀))
      = (1 - η * lam) ^ t * inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ₀) := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', inner_residual_gradientStep A y η _ hu, ih, pow_succ]
    ring

/-- **Strength zero: never learned.** If the kernel sends `u` to zero, the error along `u`
stays where it started, however long training runs. -/
theorem inner_residual_iterate_of_kernel_eq_zero (A : Θ →L[ℝ] Y) (y : Y) (η : ℝ) (θ₀ : Θ)
    {u : Y} (hu : A (adjoint A u) = 0) (t : ℕ) :
    inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y ((TAKE_GRADIENT_STEP A y η)^[t] θ₀))
      = inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ₀) := by
  have hu' : A (adjoint A u) = (0 : ℝ) • u := by rw [hu, zero_smul]
  rw [inner_residual_iterate_gradientStep A y η θ₀ hu' t]
  simp

/-- **Spectral bias.** If the kernel stretches `u` by `lam` and `η * lam ≤ 1`, then after `t`
steps the error along `u` is at least `1 - t * (η * lam)` and at most `exp (-(t * (η * lam)))`
of what it was. The clock of the direction is `1 / (η * lam)` steps. -/
theorem spectral_bias (A : Θ →L[ℝ] Y) (y : Y) {η lam : ℝ} (hle : η * lam ≤ 1) (θ₀ : Θ) {u : Y}
    (hu : A (adjoint A u) = lam • u) (t : ℕ) :
    (1 - t * (η * lam)) * |inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ₀)|
        ≤ |inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y ((TAKE_GRADIENT_STEP A y η)^[t] θ₀))|
      ∧ |inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y ((TAKE_GRADIENT_STEP A y η)^[t] θ₀))|
        ≤ Real.exp (-(t * (η * lam))) * |inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ₀)| := by
  have hshare : 0 ≤ (1 - η * lam) ^ t := pow_nonneg (by linarith) t
  rw [inner_residual_iterate_gradientStep A y η θ₀ hu t, abs_mul, abs_of_nonneg hshare]
  exact ⟨mul_le_mul_of_nonneg_right (one_sub_mul_le_pow_one_sub hle t) (abs_nonneg _),
    mul_le_mul_of_nonneg_right (pow_one_sub_le_exp hle t) (abs_nonneg _)⟩

end Direction

end SquigglyLine
