/-
Parameter distance is loss, at an exchange rate.

Say the features are tight with constant `c` when `A A† = c`: seen from the
data side they are orthogonal, each with squared length `c`. A Fourier series
with `m` terms on `n` well-spread points is nearly tight with `c = m + 1`.

Then the distance in parameter space from any start to the nearest fit is
exactly the size of the residual divided by `√c`:

    travel = ‖residual‖ / √c

So the loss and the parameter distance are one quantity in two units, and
adding parameters changes only the rate between them. With `c = 1`, which is
`n` orthonormal features for `n` points, the two are equal.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import SquigglyLine.LinearModel

namespace SquigglyLine

open ContinuousLinearMap

variable {Θ Y : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {A : Θ →L[ℝ] Y} {c : ℝ}

/-- The features are orthogonal on the data side, each with squared length `c`. -/
def TightFeatures (A : Θ →L[ℝ] Y) (c : ℝ) : Prop :=
  ∀ v, A (adjoint A v) = c • v

namespace TightFeatures

theorem norm_adjoint_sq (h : TightFeatures A c) (v : Y) : ‖adjoint A v‖ ^ 2 = c * ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, adjoint_inner_left, h v, real_inner_smul_right,
    real_inner_self_eq_norm_sq]

/-- A move of size `‖δ‖` in parameter space changes the outputs by at most `√c ‖δ‖`. -/
theorem norm_map_sq_le (h : TightFeatures A c) (hc : 0 < c) (δ : Θ) :
    ‖A δ‖ ^ 2 ≤ c * ‖δ‖ ^ 2 := by
  have hle : ‖A δ‖ ^ 2 ≤ ‖adjoint A (A δ)‖ * ‖δ‖ := by
    rw [← real_inner_self_eq_norm_sq, ← adjoint_inner_left]
    exact real_inner_le_norm _ _
  rcases eq_or_lt_of_le (sq_nonneg ‖A δ‖) with h0 | hpos
  · rw [← h0]
    positivity
  · have hsq : ‖A δ‖ ^ 2 * ‖A δ‖ ^ 2 ≤ ‖A δ‖ ^ 2 * (c * ‖δ‖ ^ 2) :=
      calc ‖A δ‖ ^ 2 * ‖A δ‖ ^ 2
          = (‖A δ‖ ^ 2) ^ 2 := (sq _).symm
        _ ≤ (‖adjoint A (A δ)‖ * ‖δ‖) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hle 2
        _ = ‖A δ‖ ^ 2 * (c * ‖δ‖ ^ 2) := by rw [mul_pow, h.norm_adjoint_sq]; ring
    exact le_of_mul_le_mul_left hsq hpos

/-- **The exchange rate.** With tight features, the distance in parameter space from the
start to the nearest fit is the size of the residual divided by `√c`. -/
theorem travel_eq (h : TightFeatures A c) (hc : 0 < c) (y : Y) (θ₀ : Θ) :
    travel (A : Θ →ₗ[ℝ] Y) y θ₀ = ‖residual (A : Θ →ₗ[ℝ] Y) y θ₀‖ / √c := by
  set r := residual (A : Θ →ₗ[ℝ] Y) y θ₀ with hr
  have hs : 0 < √c := Real.sqrt_pos.mpr hc
  rw [travel]
  refine IsLeast.csInf_eq ⟨?_, ?_⟩
  · refine ⟨θ₀ + c⁻¹ • adjoint A r, ?_, ?_⟩
    · simp only [ContinuousLinearMap.coe_coe, map_add, map_smul, h r, smul_smul,
        inv_mul_cancel₀ hc.ne', one_smul]
      simp [hr, residual]
    · have hn : ‖adjoint A r‖ = √c * ‖r‖ := by
        rw [← Real.sqrt_sq (norm_nonneg (adjoint A r)), h.norm_adjoint_sq r,
          Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg r)]
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hc.le), hn,
        eq_div_iff hs.ne',
        show c⁻¹ * (√c * ‖r‖) * √c = c⁻¹ * (√c * √c) * ‖r‖ by ring,
        Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne', one_mul]
  · rintro d ⟨θ, hθ, rfl⟩
    have hmap : A (θ - θ₀) = r := by
      have hθ' : A θ = y := hθ
      simp [hr, residual, map_sub, hθ']
    have hsq := h.norm_map_sq_le hc (θ - θ₀)
    rw [hmap] at hsq
    rw [div_le_iff₀ hs]
    calc ‖r‖
        = √(‖r‖ ^ 2) := (Real.sqrt_sq (norm_nonneg r)).symm
      _ ≤ √(c * ‖θ - θ₀‖ ^ 2) := Real.sqrt_le_sqrt hsq
      _ = ‖θ - θ₀‖ * √c := by
          rw [Real.sqrt_mul hc.le, Real.sqrt_sq (norm_nonneg _), mul_comm]

/-- **Parameter space is data space.** With orthonormal features, the distance to the nearest
fit is exactly the size of the residual. -/
theorem travel_eq_norm_residual (h : TightFeatures A 1) (y : Y) (θ₀ : Θ) :
    travel (A : Θ →ₗ[ℝ] Y) y θ₀ = ‖residual (A : Θ →ₗ[ℝ] Y) y θ₀‖ := by
  simpa using h.travel_eq one_pos y θ₀

end TightFeatures

end SquigglyLine
