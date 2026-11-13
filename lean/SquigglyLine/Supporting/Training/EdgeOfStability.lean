/-
The edge of stability.

Follow a direction `u` of the labels that the kernel stretches by `lam`. With
step size `η`, each gradient step multiplies the size of the error along `u`
by `|1 - η * lam|` (`abs_inner_residual_iterate_gradientStep`).

* `shrinks_below_edge` : if `0 < η * lam < 2` the error never grows, and the
  factor is below one (`abs_one_sub_lt_one_iff`).
* `holds_at_edge` : if `η * lam = 2` the error keeps its size for ever.
* `grows_past_edge` : if `η * lam ≥ 2` the error after `t` steps is at least
  `1 + t * (η * lam - 2)` times what it was.
* `stable_iff_lt_two_div` : a direction is stable exactly when the step size
  is below `2 / lam`.
-/
import SquigglyLine.Supporting.Training.SpectralBias

namespace SquigglyLine

/-! ### The factor `|1 - x|` -/

section Factor

/-- **The edge is at two.** The factor is below one exactly when `0 < x < 2`. -/
theorem abs_one_sub_lt_one_iff {x : ℝ} : |1 - x| < 1 ↔ 0 < x ∧ x < 2 := by
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- **Stable exactly below `2 / lam`.** -/
theorem stable_iff_lt_two_div {η lam : ℝ} (hη : 0 < η) (hlam : 0 < lam) :
    |1 - η * lam| < 1 ↔ η < 2 / lam := by
  rw [abs_one_sub_lt_one_iff, lt_div_iff₀ hlam]
  exact ⟨fun h => h.2, fun h => ⟨mul_pos hη hlam, h⟩⟩

/-- Past the edge the factor's powers grow at least linearly. -/
theorem one_add_mul_le_abs_pow {x : ℝ} (hx : 2 ≤ x) (t : ℕ) :
    1 + t * (x - 2) ≤ |1 - x| ^ t := by
  have habs : |1 - x| = 1 + (x - 2) := by
    rw [abs_of_nonpos (by linarith)]
    ring
  rw [habs]
  exact one_add_mul_le_pow (by linarith) t

end Factor

/-! ### One direction of the kernel -/

section Direction

open ContinuousLinearMap

variable {Θ Y : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- After `t` steps the size of the error along `u` is `|1 - η * lam| ^ t` times what it
was. -/
theorem abs_inner_residual_iterate_gradientStep (A : Θ →L[ℝ] Y) (y : Y) (η : ℝ) (θ₀ : Θ)
    {u : Y} {lam : ℝ} (hu : A (adjoint A u) = lam • u) (t : ℕ) :
    |inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y ((TAKE_GRADIENT_STEP A y η)^[t] θ₀))|
      = |1 - η * lam| ^ t * |inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ₀)| := by
  rw [inner_residual_iterate_gradientStep A y η θ₀ hu t, abs_mul, abs_pow]

/-- **Below the edge the error never grows.** -/
theorem shrinks_below_edge (A : Θ →L[ℝ] Y) (y : Y) {η lam : ℝ} (hpos : 0 < η * lam)
    (hlt : η * lam < 2) (θ₀ : Θ) {u : Y} (hu : A (adjoint A u) = lam • u) (t : ℕ) :
    |inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y ((TAKE_GRADIENT_STEP A y η)^[t] θ₀))|
      ≤ |inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ₀)| := by
  rw [abs_inner_residual_iterate_gradientStep A y η θ₀ hu t]
  have hfactor : |1 - η * lam| ≤ 1 := (abs_one_sub_lt_one_iff.mpr ⟨hpos, hlt⟩).le
  exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hfactor)

/-- **On the edge the error keeps its size.** It flips sign at each step and never dies
down. -/
theorem holds_at_edge (A : Θ →L[ℝ] Y) (y : Y) {η lam : ℝ} (hedge : η * lam = 2) (θ₀ : Θ)
    {u : Y} (hu : A (adjoint A u) = lam • u) (t : ℕ) :
    |inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y ((TAKE_GRADIENT_STEP A y η)^[t] θ₀))|
      = |inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ₀)| := by
  rw [abs_inner_residual_iterate_gradientStep A y η θ₀ hu t, hedge]
  norm_num

/-- **Past the edge the error grows without limit.** After `t` steps it is at least
`1 + t * (η * lam - 2)` times what it was. -/
theorem grows_past_edge (A : Θ →L[ℝ] Y) (y : Y) {η lam : ℝ} (hpast : 2 ≤ η * lam) (θ₀ : Θ)
    {u : Y} (hu : A (adjoint A u) = lam • u) (t : ℕ) :
    (1 + t * (η * lam - 2)) * |inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ₀)|
      ≤ |inner ℝ u (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y ((TAKE_GRADIENT_STEP A y η)^[t] θ₀))| := by
  rw [abs_inner_residual_iterate_gradientStep A y η θ₀ hu t]
  exact mul_le_mul_of_nonneg_right (one_add_mul_le_abs_pow hpast t) (abs_nonneg _)

end Direction

end SquigglyLine
