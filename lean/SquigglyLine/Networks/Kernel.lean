/-
The bridge, part 2: for training, a model is its kernel.

Take a model whose outputs on the data are linear in its weights: a Fourier
series in its coefficients, or a ReLU network in its last layer. Write
`predict` for the map from weights to outputs. The kernel is
`predict (adjoint predict vector)`, that is `K = A A†` with `A = predict`.

* `residual_gradientStep`: one gradient step sends the error `residual` to
  `residual - learning_rate • K residual`. The weights do not appear.
* `travel_eq_norm_of_kernelInverse`: the distance to the nearest fit is the
  length of `A† K⁻¹ residual`, whose square is `⟪K⁻¹ residual, residual⟫`.

So two models with the same kernel are the same learner
(`residual_iterate_gradientStep_eq`, `travel_eq_of_kernel_eq`): gradient
descent takes them through the same errors, and their nearest fits are equally
far away. This is the exact sense in which the Fourier model and the ReLU
model can be equivalent.

* `TAKE_GRADIENT_STEP`                  one step of gradient descent;
* `residual_gradientStep`               one step, seen on the residual;
* `norm_adjoint_kernelInverse_sq`       the squared length of `A† K⁻¹ residual`;
* `travel_eq_norm_of_kernelInverse`     travel is the length of
                                        `A† K⁻¹ residual`;
* `residual_iterate_gradientStep_eq`    same kernel, same training path;
* `travel_eq_of_kernel_eq`              same kernel, same travel.
-/
import SquigglyLine.Networks.ExchangeRate

namespace SquigglyLine

open ContinuousLinearMap

variable {Weights OtherWeights Outputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup OtherWeights] [InnerProductSpace ℝ OtherWeights]
  [CompleteSpace OtherWeights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]

/-- One step of gradient descent on the squared error
`‖labels - predict weights‖² / 2`.
Python: `weights + learning_rate * predict.T @ (labels - predict @ weights)`. -/
noncomputable def TAKE_GRADIENT_STEP
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (weights : Weights) : Weights :=
  weights + learning_rate
    • adjoint predict
        (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights)

/-- **Gradient descent sees only the kernel.** One step sends the error
`residual` to `residual - learning_rate • K residual`. -/
theorem residual_gradientStep
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (weights : Weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let stepped_weights :=
      TAKE_GRADIENT_STEP predict labels learning_rate weights
    let residual_after := GET_RESIDUAL linear_predict labels stepped_weights
    let residual_before := GET_RESIDUAL linear_predict labels weights
    let kernel_applied  := predict (adjoint predict residual_before)  -- `K r`, with `K = A A†`
    residual_after = residual_before - learning_rate • kernel_applied := by
  unfold_named_pieces
  simp only [GET_RESIDUAL, TAKE_GRADIENT_STEP, ContinuousLinearMap.coe_coe,
    map_add, map_smul]
  abel

/-- The squared length of `A† K⁻¹ residual` is `⟪K⁻¹ residual, residual⟫`: it
depends on the kernel only. -/
theorem norm_adjoint_kernelInverse_sq
    (predict : Weights →L[ℝ] Outputs)
    (kernel_inverse : Outputs → Outputs)
    (kernel_inverse_works : ∀ vector,
      predict (adjoint predict (kernel_inverse vector)) = vector)
    (residual : Outputs) :
    let pullback_size := ‖adjoint predict (kernel_inverse residual)‖ ^ 2
    let kernel_form   := inner ℝ (kernel_inverse residual) residual
    pullback_size = kernel_form := by
  unfold_named_pieces
  rw [← real_inner_self_eq_norm_sq, adjoint_inner_left,
    kernel_inverse_works residual]

/-- **Travel sees only the kernel.** If `kernel_inverse` inverts the kernel,
the distance from the start to the nearest fit is the length of
`A† K⁻¹ residual`. -/
theorem travel_eq_norm_of_kernelInverse
    (predict : Weights →L[ℝ] Outputs)
    (kernel_inverse : Outputs → Outputs)
    (kernel_inverse_works : ∀ vector,
      predict (adjoint predict (kernel_inverse vector)) = vector)
    (labels : Outputs)
    (start_weights : Weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let travel   := GET_TRAVEL linear_predict labels start_weights
    let residual := GET_RESIDUAL linear_predict labels start_weights
    let pullback := adjoint predict (kernel_inverse residual)  -- the move that cancels the residual
    travel = ‖pullback‖ := by
  unfold_named_pieces
  obtain ⟨residual, residual_def⟩ : ∃ residual,
      residual = GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
        start_weights :=
    ⟨_, rfl⟩
  rw [← residual_def, GET_TRAVEL]
  refine IsLeast.csInf_eq ⟨⟨start_weights + adjoint predict
    (kernel_inverse residual), ?_, by simp⟩, ?_⟩
  · simp only [ContinuousLinearMap.coe_coe, map_add,
      kernel_inverse_works residual]
    simp [residual_def, GET_RESIDUAL]
  · -- Any fit must cancel the same residual; among such moves the one along
    -- the features is the shortest.
    rintro distance ⟨weights, weights_fit, rfl⟩
    have step_gives_residual :
        predict (weights - start_weights) = residual := by
      have predict_weights : predict weights = labels := weights_fit
      simp [residual_def, GET_RESIDUAL, map_sub, predict_weights]
    have pullback_form_eq :
        inner ℝ (adjoint predict (kernel_inverse residual))
          (weights - start_weights)
        = inner ℝ (kernel_inverse residual) residual := by
      rw [adjoint_inner_left, step_gives_residual]
    have squared_le : ‖adjoint predict (kernel_inverse residual)‖ ^ 2
        ≤ ‖adjoint predict (kernel_inverse residual)‖
          * ‖weights - start_weights‖ := by
      have squared_eq : ‖adjoint predict (kernel_inverse residual)‖ ^ 2
          = inner ℝ (kernel_inverse residual) residual :=
        norm_adjoint_kernelInverse_sq predict kernel_inverse
          kernel_inverse_works residual
      rw [squared_eq, ← pullback_form_eq]
      exact real_inner_le_norm _ _
    rcases eq_or_lt_of_le
      (norm_nonneg (adjoint predict (kernel_inverse residual)))
      with zero | positive
    · rw [← zero]
      exact norm_nonneg _
    · rw [sq] at squared_le
      exact le_of_mul_le_mul_left squared_le positive

variable {predict : Weights →L[ℝ] Outputs}
  {other_predict : OtherWeights →L[ℝ] Outputs}

/-- **Same kernel, same training path.** If two models have the same kernel
and start with the same error, gradient descent keeps their errors equal at
every step. -/
theorem residual_iterate_gradientStep_eq
    (same_kernel : ∀ vector,
      predict (adjoint predict vector)
        = other_predict (adjoint other_predict vector))
    (labels : Outputs)
    (learning_rate : ℝ)
    {weights : Weights}
    {other_weights : OtherWeights}
    (same_start_residual :
      GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights
        = GET_RESIDUAL (other_predict : OtherWeights →ₗ[ℝ] Outputs) labels
            other_weights)
    (step_count : ℕ) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let other_linear_predict : LinearPredictor OtherWeights Outputs :=
      other_predict
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count] weights
    let other_trained_weights :=
      (TAKE_GRADIENT_STEP other_predict labels learning_rate)^[step_count]
        other_weights
    let residual       := GET_RESIDUAL linear_predict labels trained_weights
    let other_residual :=
      GET_RESIDUAL other_linear_predict labels other_trained_weights
    residual = other_residual := by
  unfold_named_pieces
  induction step_count with
  | zero => exact same_start_residual
  | succ previous_count earlier_case =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      residual_gradientStep, residual_gradientStep, earlier_case,
      same_kernel]

/-- **Same kernel, same travel.** If two models have the same invertible
kernel and start with the same error, their nearest fits are equally far away
in parameter space. -/
theorem travel_eq_of_kernel_eq
    (same_kernel : ∀ vector,
      predict (adjoint predict vector)
        = other_predict (adjoint other_predict vector))
    (kernel_inverse : Outputs → Outputs)
    (kernel_inverse_works : ∀ vector,
      predict (adjoint predict (kernel_inverse vector)) = vector)
    (labels : Outputs)
    {weights : Weights}
    {other_weights : OtherWeights}
    (same_start_residual :
      GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights
        = GET_RESIDUAL (other_predict : OtherWeights →ₗ[ℝ] Outputs) labels
            other_weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let other_linear_predict : LinearPredictor OtherWeights Outputs :=
      other_predict
    let travel       := GET_TRAVEL linear_predict labels weights
    let other_travel := GET_TRAVEL other_linear_predict labels other_weights
    travel = other_travel := by
  unfold_named_pieces
  have other_kernel_inverse_works : ∀ vector,
      other_predict (adjoint other_predict (kernel_inverse vector)) = vector :=
    fun vector => (same_kernel _).symm.trans (kernel_inverse_works vector)
  rw [travel_eq_norm_of_kernelInverse predict kernel_inverse
      kernel_inverse_works,
    travel_eq_norm_of_kernelInverse other_predict kernel_inverse
      other_kernel_inverse_works,
    ← same_start_residual]
  -- Two lengths are equal once their squares are, and both squares are
  -- `⟪K⁻¹ residual, residual⟫`.
  refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
  have squared_eq : ‖adjoint predict (kernel_inverse
        (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights))‖ ^ 2
      = inner ℝ (kernel_inverse
          (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights))
        (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights) :=
    norm_adjoint_kernelInverse_sq predict kernel_inverse
      kernel_inverse_works _
  have other_squared_eq : ‖adjoint other_predict (kernel_inverse
        (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights))‖ ^ 2
      = inner ℝ (kernel_inverse
          (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights))
        (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights) :=
    norm_adjoint_kernelInverse_sq other_predict kernel_inverse
      other_kernel_inverse_works _
  rw [squared_eq, other_squared_eq]

end SquigglyLine
