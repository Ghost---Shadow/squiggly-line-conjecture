/-
Bias and variance, and what the dial is.

A fit's answer at a new input is off by a fixed part (the bias) and a part
that follows the noise. A floor `mu` is added to the strength of every
direction.

* `bias_variance` : if the noise part is zero on average, the expected squared
  error is the bias squared plus the variance.
* `signal_term_sub` : the bias. A floor `mu` shrinks the signal term by the
  factor `mu / (lamS + mu)`.
* `expected_sq_error` : the two together, for a signal along a direction of
  strength `lamS` and noise along one of strength `lamE`.
* `bias_factor_mono` : raising the floor raises the bias.
* `variance_factor_anti` : raising the floor lowers the variance.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace SquigglyLine

open MeasureTheory

/-! ### The two factors -/

section Factors

/-- **The bias.** A floor `mu` shrinks the signal term by the factor `mu / (lamS + mu)`. -/
theorem signal_term_sub (x : ℝ) {lamS mu : ℝ} (hlamS : lamS ≠ 0) (hsum : lamS + mu ≠ 0) :
    x / (lamS + mu) - x / lamS = -(x / lamS * (mu / (lamS + mu))) := by
  field_simp
  ring

/-- **Raising the floor raises the bias.** -/
theorem bias_factor_mono {lamS mu₁ mu₂ : ℝ} (hlamS : 0 < lamS) (h1 : 0 ≤ mu₁)
    (h12 : mu₁ ≤ mu₂) : mu₁ / (lamS + mu₁) ≤ mu₂ / (lamS + mu₂) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- **Raising the floor lowers the variance.** -/
theorem variance_factor_anti {lamE mu₁ mu₂ : ℝ} (hlamE : 0 ≤ lamE) (h1 : 0 < mu₁)
    (h12 : mu₁ ≤ mu₂) : 1 / (lamE + mu₂) ≤ 1 / (lamE + mu₁) :=
  one_div_le_one_div_of_le (by linarith) (by linarith)

end Factors

/-! ### They add -/

section Split

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- **Bias squared plus variance.** If `Z` is zero on average, the expected square of
`b + Z` is `b²` plus the expected square of `Z`. -/
theorem bias_variance {Z : Ω → ℝ} (hZ : Integrable Z P)
    (hZ2 : Integrable (fun ω => Z ω ^ 2) P) (hmean : ∫ ω, Z ω ∂P = 0) (b : ℝ) :
    ∫ ω, (b + Z ω) ^ 2 ∂P = b ^ 2 + ∫ ω, Z ω ^ 2 ∂P := by
  have hexpand : (fun ω => (b + Z ω) ^ 2) = fun ω => b ^ 2 + 2 * b * Z ω + Z ω ^ 2 := by
    funext ω
    ring
  have hcross : Integrable (fun ω => 2 * b * Z ω) P := hZ.const_mul _
  have hconst : Integrable (fun _ : Ω => b ^ 2) P := integrable_const _
  have hsplit₁ : ∫ ω, b ^ 2 + 2 * b * Z ω + Z ω ^ 2 ∂P
      = (∫ ω, b ^ 2 + 2 * b * Z ω ∂P) + ∫ ω, Z ω ^ 2 ∂P :=
    integral_add (hconst.add hcross) hZ2
  have hsplit₂ : ∫ ω, b ^ 2 + 2 * b * Z ω ∂P = (∫ _ω, b ^ 2 ∂P) + ∫ ω, 2 * b * Z ω ∂P :=
    integral_add hconst hcross
  rw [hexpand, hsplit₁, hsplit₂, integral_const_mul, hmean]
  simp

/-- **The split for a signal and a noise.** The signal has overlap `x` with the new input
and lies along a direction of strength `lamS`. The noise has overlap `N`, a random number
that is zero on average, and lies along a direction of strength `lamE`. With a floor `mu`,
the expected squared error at the new input is the bias squared plus the variance. -/
theorem expected_sq_error {N : Ω → ℝ} (hN : Integrable N P)
    (hN2 : Integrable (fun ω => N ω ^ 2) P) (hmean : ∫ ω, N ω ∂P = 0) (x : ℝ)
    {lamS lamE mu : ℝ} (hlamS : lamS ≠ 0) (hsum : lamS + mu ≠ 0) :
    ∫ ω, (x / (lamS + mu) + N ω / (lamE + mu) - x / lamS) ^ 2 ∂P
      = (x / lamS * (mu / (lamS + mu))) ^ 2 + (∫ ω, N ω ^ 2 ∂P) / (lamE + mu) ^ 2 := by
  have hshape : (fun ω => (x / (lamS + mu) + N ω / (lamE + mu) - x / lamS) ^ 2)
      = fun ω => (-(x / lamS * (mu / (lamS + mu))) + N ω / (lamE + mu)) ^ 2 := by
    funext ω
    rw [← signal_term_sub x hlamS hsum]
    ring
  have hZ : Integrable (fun ω => N ω / (lamE + mu)) P := hN.div_const _
  have hZ2 : Integrable (fun ω => (N ω / (lamE + mu)) ^ 2) P := by
    simp_rw [div_pow]
    exact hN2.div_const _
  have hZmean : ∫ ω, N ω / (lamE + mu) ∂P = 0 := by
    rw [integral_div, hmean, zero_div]
  rw [hshape, bias_variance P hZ hZ2 hZmean, neg_sq]
  simp_rw [div_pow]
  rw [integral_div]

end Split

end SquigglyLine
