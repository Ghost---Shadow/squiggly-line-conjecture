/-
The bridge, part 2: for training, a model is its kernel.

Take a model whose outputs on the data are linear in its weights: a Fourier
series in its coefficients, or a ReLU network in its last layer. Write `A` for
the map from weights to outputs. The kernel is `K = A A†`.

* `residual_gradientStep`: one gradient step sends the error `r` to
  `r - η K r`. The weights do not appear.
* `travel_eq_norm_of_kernelInverse`: the distance to the nearest fit is the
  length of `A† K⁻¹ r`, whose square is `⟪K⁻¹ r, r⟫`.

So two models with the same kernel are the same learner
(`residual_iterate_gradientStep_eq`, `travel_eq_of_kernel_eq`): gradient
descent takes them through the same errors, and their nearest fits are equally
far away. This is the exact sense in which the Fourier model and the ReLU
model can be equivalent.
-/
import SquigglyLine.Networks.ExchangeRate

namespace SquigglyLine

open ContinuousLinearMap

variable {Θ Θ' Y : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Θ'] [InnerProductSpace ℝ Θ'] [CompleteSpace Θ']
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- One step of gradient descent on the squared error `‖y - A θ‖² / 2`. -/
noncomputable def TAKE_GRADIENT_STEP (A : Θ →L[ℝ] Y) (y : Y) (η : ℝ) (θ : Θ) : Θ :=
  θ + η • adjoint A (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ)

/-- **Gradient descent sees only the kernel.** One step sends the error `r` to `r - η K r`. -/
theorem residual_gradientStep (A : Θ →L[ℝ] Y) (y : Y) (η : ℝ) (θ : Θ) :
    GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y (TAKE_GRADIENT_STEP A y η θ)
      = GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ
        - η • A (adjoint A (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ)) := by
  simp only [GET_RESIDUAL, TAKE_GRADIENT_STEP, ContinuousLinearMap.coe_coe, map_add, map_smul]
  abel

/-- The squared length of `A† K⁻¹ r` is `⟪K⁻¹ r, r⟫`: it depends on the kernel only. -/
theorem norm_adjoint_kernelInverse_sq (A : Θ →L[ℝ] Y) (Kinv : Y → Y)
    (hinv : ∀ v, A (adjoint A (Kinv v)) = v) (r : Y) :
    ‖adjoint A (Kinv r)‖ ^ 2 = inner ℝ (Kinv r) r := by
  rw [← real_inner_self_eq_norm_sq, adjoint_inner_left, hinv r]

/-- **Travel sees only the kernel.** If `Kinv` inverts the kernel, the distance from the
start to the nearest fit is the length of `A† K⁻¹ r`. -/
theorem travel_eq_norm_of_kernelInverse (A : Θ →L[ℝ] Y) (Kinv : Y → Y)
    (hinv : ∀ v, A (adjoint A (Kinv v)) = v) (y : Y) (θ₀ : Θ) :
    GET_TRAVEL (A : Θ →ₗ[ℝ] Y) y θ₀
      = ‖adjoint A (Kinv (GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ₀))‖ := by
  obtain ⟨r, hr⟩ : ∃ r, r = GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ₀ := ⟨_, rfl⟩
  rw [← hr, GET_TRAVEL]
  refine IsLeast.csInf_eq ⟨⟨θ₀ + adjoint A (Kinv r), ?_, by simp⟩, ?_⟩
  · simp only [ContinuousLinearMap.coe_coe, map_add, hinv r]
    simp [hr, GET_RESIDUAL]
  · rintro d ⟨θ, hθ, rfl⟩
    have hmap : A (θ - θ₀) = r := by
      have hθ' : A θ = y := hθ
      simp [hr, GET_RESIDUAL, map_sub, hθ']
    have hinner : inner ℝ (adjoint A (Kinv r)) (θ - θ₀) = inner ℝ (Kinv r) r := by
      rw [adjoint_inner_left, hmap]
    have hle : ‖adjoint A (Kinv r)‖ ^ 2 ≤ ‖adjoint A (Kinv r)‖ * ‖θ - θ₀‖ := by
      rw [norm_adjoint_kernelInverse_sq A Kinv hinv r, ← hinner]
      exact real_inner_le_norm _ _
    rcases eq_or_lt_of_le (norm_nonneg (adjoint A (Kinv r))) with h0 | hpos
    · rw [← h0]
      exact norm_nonneg _
    · rw [sq] at hle
      exact le_of_mul_le_mul_left hle hpos

variable {A : Θ →L[ℝ] Y} {B : Θ' →L[ℝ] Y}

/-- **Same kernel, same training path.** If two models have the same kernel and start with
the same error, gradient descent keeps their errors equal at every step. -/
theorem residual_iterate_gradientStep_eq (hK : ∀ v, A (adjoint A v) = B (adjoint B v))
    (y : Y) (η : ℝ) {θ : Θ} {θ' : Θ'}
    (h : GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ = GET_RESIDUAL (B : Θ' →ₗ[ℝ] Y) y θ') (t : ℕ) :
    GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y ((TAKE_GRADIENT_STEP A y η)^[t] θ)
      = GET_RESIDUAL (B : Θ' →ₗ[ℝ] Y) y ((TAKE_GRADIENT_STEP B y η)^[t] θ') := by
  induction t with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', residual_gradientStep,
      residual_gradientStep, ih, hK]

/-- **Same kernel, same travel.** If two models have the same invertible kernel and start
with the same error, their nearest fits are equally far away in parameter space. -/
theorem travel_eq_of_kernel_eq (hK : ∀ v, A (adjoint A v) = B (adjoint B v)) (Kinv : Y → Y)
    (hinv : ∀ v, A (adjoint A (Kinv v)) = v) (y : Y) {θ : Θ} {θ' : Θ'}
    (h : GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ = GET_RESIDUAL (B : Θ' →ₗ[ℝ] Y) y θ') :
    GET_TRAVEL (A : Θ →ₗ[ℝ] Y) y θ = GET_TRAVEL (B : Θ' →ₗ[ℝ] Y) y θ' := by
  have hinvB : ∀ v, B (adjoint B (Kinv v)) = v := fun v => (hK _).symm.trans (hinv v)
  rw [travel_eq_norm_of_kernelInverse A Kinv hinv, travel_eq_norm_of_kernelInverse B Kinv hinvB,
    ← h]
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  rw [norm_adjoint_kernelInverse_sq A Kinv hinv, norm_adjoint_kernelInverse_sq B Kinv hinvB]

end SquigglyLine
