/-
Benign overfitting: fitting the noise without paying for it.

What is left to fit splits into a signal `s` and a noise `ε`, along kernel
directions of strengths `μs` and `μe`. `splitFit` is the fit gradient descent
heads for.

* `splitFit_fits`, `splitFit_is_nearest` : it fits signal and noise exactly,
  and no fit is nearer to the start.
* `inner_splitFit` : at a new input the answer moves by the signal's overlap
  divided by `μs` plus the noise's overlap divided by `μe`.
* `abs_noise_damage_le` : with junk features of strength `c'` in every
  direction, the noise term is at most the overlap divided by `c'`.
* `abs_signal_loss_le` : and the signal term changes by at most the fraction
  `c' / lamS` of itself.
* `benign_overfitting` : the three together.
-/
import SquigglyLine.Supporting.Training.LeastAction
import SquigglyLine.Supporting.NewInputs.Pruning

namespace SquigglyLine

open ContinuousLinearMap

/-! ### The two terms -/

section Terms

/-- **The damage is capped by the junk.** A noise direction of any strength `lamE ≥ 0`,
after junk features add `c'`, moves a new answer by at most the overlap over `c'`. -/
theorem abs_div_add_le {x bound lamE c' : ℝ} (hx : |x| ≤ bound) (hlamE : 0 ≤ lamE)
    (hc' : 0 < c') : |x / (lamE + c')| ≤ bound / c' := by
  have hpos : 0 < lamE + c' := by linarith
  calc |x / (lamE + c')| = |x| / (lamE + c') := by rw [abs_div, abs_of_pos hpos]
    _ ≤ |x| / c' := div_le_div_of_nonneg_left (abs_nonneg _) hc' (by linarith)
    _ ≤ bound / c' := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hx (inv_nonneg.mpr hc'.le)

/-- **The signal is nearly untouched.** Adding `c'` to a strong direction changes its term
by at most the fraction `c' / lamS` of itself. -/
theorem abs_signal_loss_le (x : ℝ) {lamS c' : ℝ} (hlamS : 0 < lamS) (hc' : 0 ≤ c') :
    |x / lamS - x / (lamS + c')| ≤ |x / lamS| * (c' / lamS) := by
  have hsum : 0 < lamS + c' := by linarith
  have hdiff : x / lamS - x / (lamS + c') = x / lamS * (c' / (lamS + c')) := by
    field_simp
    ring
  rw [hdiff, abs_mul, abs_of_nonneg (div_nonneg hc' hsum.le)]
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hc' hlamS (by linarith))
    (abs_nonneg _)

end Terms

/-! ### The fit that swallows the noise -/

section Fit

variable {Ξ Y : Type*}
  [NormedAddCommGroup Ξ] [InnerProductSpace ℝ Ξ] [CompleteSpace Ξ]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The fit that gradient descent heads for when the residual is a signal `s` plus a noise
`ε`, along kernel directions of strengths `μs` and `μe`. -/
noncomputable def splitFit (C : Ξ →L[ℝ] Y) (ξ₀ : Ξ) (s ε : Y) (μs μe : ℝ) : Ξ :=
  ξ₀ + adjoint C (μs⁻¹ • s + μe⁻¹ • ε)

/-- **It fits the signal and the noise exactly.** -/
theorem splitFit_fits (C : Ξ →L[ℝ] Y) (y : Y) (ξ₀ : Ξ) {s ε : Y} {μs μe : ℝ} (hμs : μs ≠ 0)
    (hμe : μe ≠ 0) (hs : C (adjoint C s) = μs • s) (he : C (adjoint C ε) = μe • ε)
    (hsplit : residual (C : Ξ →ₗ[ℝ] Y) y ξ₀ = s + ε) :
    C (splitFit C ξ₀ s ε μs μe) = y := by
  simp only [splitFit, map_add, map_smul, hs, he, smul_smul, inv_mul_cancel₀ hμs,
    inv_mul_cancel₀ hμe, one_smul]
  rw [← hsplit]
  simp [residual]

/-- **No fit is nearer.** -/
theorem splitFit_is_nearest (C : Ξ →L[ℝ] Y) {y : Y} (ξ₀ : Ξ) (s ε : Y) (μs μe : ℝ)
    (hfit : C (splitFit C ξ₀ s ε μs μe) = y) {ξ' : Ξ} (hfit' : C ξ' = y) :
    ‖splitFit C ξ₀ s ε μs μe - ξ₀‖ ≤ ‖ξ' - ξ₀‖ :=
  norm_sub_le_of_fit_along_features C rfl hfit hfit'

/-- **What the fit does to a new input.** The answer at `ψ` moves by the signal's overlap
with the test row divided by `μs`, plus the noise's overlap divided by `μe`. -/
theorem inner_splitFit (C : Ξ →L[ℝ] Y) (ξ₀ ψ : Ξ) (s ε : Y) (μs μe : ℝ) :
    inner ℝ ψ (splitFit C ξ₀ s ε μs μe)
      = inner ℝ ψ ξ₀ + inner ℝ (C ψ) s / μs + inner ℝ (C ψ) ε / μe := by
  rw [splitFit, inner_add_right, adjoint_inner_right, inner_add_right, real_inner_smul_right,
    real_inner_smul_right]
  ring

end Fit

/-! ### With junk features -/

section Junk

variable {Θ Θ' Ξ Y : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Θ'] [InnerProductSpace ℝ Θ'] [CompleteSpace Θ']
  [NormedAddCommGroup Ξ] [InnerProductSpace ℝ Ξ] [CompleteSpace Ξ]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  {C : Ξ →L[ℝ] Y} {A : Θ →L[ℝ] Y} {B : Θ' →L[ℝ] Y}

omit [CompleteSpace Ξ] [CompleteSpace Y] in
/-- The damage the noise does to the answer at a new input. -/
theorem abs_noise_damage_le (C : Ξ →L[ℝ] Y) (ψ : Ξ) (ε : Y) {lamE c' : ℝ} (hlamE : 0 ≤ lamE)
    (hc' : 0 < c') : |inner ℝ (C ψ) ε / (lamE + c')| ≤ ‖C ψ‖ * ‖ε‖ / c' :=
  abs_div_add_le (abs_real_inner_le_norm _ _) hlamE hc'

/-- **Benign overfitting.** The whole model `C` has real features `A` and junk features `B`
of strength `c'` in every direction. The signal lies along a direction of strength `lamS`
of the real features and the noise along one of strength `lamE`. Then the nearest fit of
the whole model fits signal and noise exactly; it moves the answer at a new input by the
two terms below; and the noise term is at most `‖C ψ‖ * ‖ε‖ / c'`, however weak `lamE`
is. -/
theorem benign_overfitting (hsum : KernelSum C A B) {c' : ℝ} (hc' : 0 < c')
    (hB : TightFeatures B c') {s ε : Y} {lamS lamE : ℝ} (hlamS : 0 < lamS) (hlamE : 0 ≤ lamE)
    (hs : A (adjoint A s) = lamS • s) (he : A (adjoint A ε) = lamE • ε) (y : Y) (ξ₀ : Ξ)
    (hsplit : residual (C : Ξ →ₗ[ℝ] Y) y ξ₀ = s + ε) (ψ : Ξ) :
    C (splitFit C ξ₀ s ε (lamS + c') (lamE + c')) = y
      ∧ inner ℝ ψ (splitFit C ξ₀ s ε (lamS + c') (lamE + c'))
          = inner ℝ ψ ξ₀ + inner ℝ (C ψ) s / (lamS + c') + inner ℝ (C ψ) ε / (lamE + c')
      ∧ |inner ℝ (C ψ) ε / (lamE + c')| ≤ ‖C ψ‖ * ‖ε‖ / c' :=
  ⟨splitFit_fits C y ξ₀ (ne_of_gt (by linarith)) (ne_of_gt (by linarith))
      (kernel_eigen_add hsum hs (hB s)) (kernel_eigen_add hsum he (hB ε)) hsplit,
    inner_splitFit C ξ₀ ψ s ε _ _, abs_noise_damage_le C ψ ε hlamE hc'⟩

end Junk

end SquigglyLine
