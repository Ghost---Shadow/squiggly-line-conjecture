/-
Lottery tickets: what pruning costs.

Split a model's weights into the kept ones (features `A`) and the dropped ones
(features `B`). The whole model `C` has both. Its kernel is the sum of the two
kernels (`KernelSum`).

* `kernel_eigen_add` : along a direction where the kept weights have strength
  `lam` and the dropped weights have strength `mu`, the whole model has
  strength `lam + mu`.
* `pruned_share_ge` : the pruned model has at least as large a share of its
  error left along that direction, at every step.
* `winning_ticket` : if the dropped weights have no strength along a
  direction, the pruned model and the whole model keep the same error there
  at every step.
* `travel_mul_sqrt_pruned` : with orthogonal features of strengths `c` and
  `c'`, pruning moves the nearest fit farther by `√((c + c') / c)`.
-/
import SquigglyLine.Supporting.Training.SpectralBias

namespace SquigglyLine

open ContinuousLinearMap

variable {Θ Θ' Ξ Y : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Θ'] [InnerProductSpace ℝ Θ'] [CompleteSpace Θ']
  [NormedAddCommGroup Ξ] [InnerProductSpace ℝ Ξ] [CompleteSpace Ξ]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The whole model `C` has the kept features `A` and the dropped features `B` side by side:
its kernel is the sum of their kernels. -/
def KernelSum (C : Ξ →L[ℝ] Y) (A : Θ →L[ℝ] Y) (B : Θ' →L[ℝ] Y) : Prop :=
  ∀ v, C (adjoint C v) = A (adjoint A v) + B (adjoint B v)

variable {C : Ξ →L[ℝ] Y} {A : Θ →L[ℝ] Y} {B : Θ' →L[ℝ] Y}

/-- **Strengths add.** -/
theorem kernel_eigen_add (hsum : KernelSum C A B) {u : Y} {lam mu : ℝ}
    (hA : A (adjoint A u) = lam • u) (hB : B (adjoint B u) = mu • u) :
    C (adjoint C u) = (lam + mu) • u := by
  rw [hsum u, hA, hB, add_smul]

/-- **Pruning slows a direction down.** With step size `η`, the share of the error left
along a direction is at least as large for the pruned model as for the whole model. -/
theorem pruned_share_ge {η lam mu : ℝ} (hη : 0 ≤ η) (hmu : 0 ≤ mu)
    (hle : η * (lam + mu) ≤ 1) (t : ℕ) : (1 - η * (lam + mu)) ^ t ≤ (1 - η * lam) ^ t :=
  strong_directions_first hη (by linarith) hle t

/-- **A winning ticket.** If the dropped weights have no strength along `u`, then the pruned
model and the whole model, started with the same error along `u`, keep the same error along
`u` at every step of gradient descent. -/
theorem winning_ticket (hsum : KernelSum C A B) (y : Y) (η : ℝ) {u : Y} {lam : ℝ}
    (hA : A (adjoint A u) = lam • u) (hB : B (adjoint B u) = 0) {θ : Θ} {ξ : Ξ}
    (hstart : inner ℝ u (residual (A : Θ →ₗ[ℝ] Y) y θ)
      = inner ℝ u (residual (C : Ξ →ₗ[ℝ] Y) y ξ)) (t : ℕ) :
    inner ℝ u (residual (A : Θ →ₗ[ℝ] Y) y ((gradientStep A y η)^[t] θ))
      = inner ℝ u (residual (C : Ξ →ₗ[ℝ] Y) y ((gradientStep C y η)^[t] ξ)) := by
  have hC : C (adjoint C u) = lam • u := by rw [hsum u, hA, hB, add_zero]
  rw [inner_residual_iterate_gradientStep A y η θ hA t,
    inner_residual_iterate_gradientStep C y η ξ hC t, hstart]

/-- With orthogonal features on both sides, the whole model has orthogonal features too, and
the strengths add. -/
theorem TightFeatures.of_kernelSum (hsum : KernelSum C A B) {c c' : ℝ}
    (hA : TightFeatures A c) (hB : TightFeatures B c') : TightFeatures C (c + c') := by
  intro v
  rw [hsum v, hA v, hB v, add_smul]

/-- **Pruning moves the fit farther.** With orthogonal features of strengths `c` (kept) and
`c'` (dropped), and the same error at the start, the travel of the pruned model times `√c` is
the travel of the whole model times `√(c + c')`. -/
theorem travel_mul_sqrt_pruned (hsum : KernelSum C A B) {c c' : ℝ} (hc : 0 < c) (hc' : 0 ≤ c')
    (hA : TightFeatures A c) (hB : TightFeatures B c') (y : Y) {θ : Θ} {ξ : Ξ}
    (hstart : residual (A : Θ →ₗ[ℝ] Y) y θ = residual (C : Ξ →ₗ[ℝ] Y) y ξ) :
    travel (A : Θ →ₗ[ℝ] Y) y θ * √c = travel (C : Ξ →ₗ[ℝ] Y) y ξ * √(c + c') := by
  have hcc : 0 < c + c' := by linarith
  rw [hA.travel_eq hc, (TightFeatures.of_kernelSum hsum hA hB).travel_eq hcc, hstart,
    div_mul_cancel₀ _ (Real.sqrt_pos.mpr hc).ne', div_mul_cancel₀ _ (Real.sqrt_pos.mpr hcc).ne']

end SquigglyLine
