/-
Flat minima: flatter is farther.

Rescale a model: multiply its parameters by `scale`, and divide them by `scale`
before use. Nothing it computes changes.

* `rescale_smul`, `residual_rescale` : same outputs, same error.
* `norm_rescale_sq`, `kernel_rescale` : the loss is flatter by `scale²`.
* `travel_rescale` : the nearest fit is farther by `|scale|`.
* `gradientStep_rescale` : a gradient step of the rescaled model is a step of
  the old one with step size `learning_rate / scale²`.
* `strength_mul_travel_sq` : what does not change. Along a direction of
  strength `kernel_strength`, strength times travel squared is the error
  squared.

Definition and theorems:

* `RESCALE`                  the model with its parameters in other units;
* `rescale_smul`             the same outputs;
* `residual_rescale`         the same error;
* `norm_rescale_sq`          flatter by `scale²`;
* `fitDistances_rescale`     the distances to the fits are multiplied by
                             `|scale|`;
* `travel_rescale`           the nearest fit is farther by `|scale|`;
* `flatter_is_farther`       the three facts together;
* `adjoint_rescale`          the adjoint of the rescaled model;
* `kernel_rescale`           the kernel is weaker by `scale²`;
* `gradientStep_rescale`     rescaling is a change of step size;
* `strength_mul_travel_sq`   strength times travel squared does not change.
-/
import SquigglyLine.Networks.DoubleDescent

namespace SquigglyLine

open scoped Pointwise

/-! ### The same model in other units -/

section Units

variable {Weights Outputs : Type*}
  [NormedAddCommGroup Weights] [NormedSpace ℝ Weights]
  [NormedAddCommGroup Outputs] [NormedSpace ℝ Outputs]

/-- The model `predict` with its parameters measured in units `scale` times
smaller: the new parameters are `scale` times the old ones, and are divided by
`scale` before use. -/
noncomputable def RESCALE
    (scale : ℝ)
    (predict : Weights →L[ℝ] Outputs) : Weights →L[ℝ] Outputs :=
  scale⁻¹ • predict

/-- **Same outputs.** The rescaled model at `scale • weights` gives what the
model gave at `weights`. -/
theorem rescale_smul
    {scale : ℝ}
    (scale_ne_zero : scale ≠ 0)
    (predict : Weights →L[ℝ] Outputs)
    (weights : Weights) :
    let rescaled_output := RESCALE scale predict (scale • weights)
    let output          := predict weights
    rescaled_output = output := by
  unfold_named_pieces
  rw [RESCALE, smul_apply, map_smul, inv_smul_smul₀ scale_ne_zero]

/-- **Same error.** -/
theorem residual_rescale
    {scale : ℝ}
    (scale_ne_zero : scale ≠ 0)
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (weights : Weights) :
    let rescaled_predict : LinearPredictor Weights Outputs :=
      RESCALE scale predict
    let linear_predict : LinearPredictor Weights Outputs := predict
    let rescaled_residual :=
      GET_RESIDUAL rescaled_predict labels (scale • weights)
    let residual          := GET_RESIDUAL linear_predict labels weights
    rescaled_residual = residual := by
  unfold_named_pieces
  have same_output :
      RESCALE scale predict (scale • weights) = predict weights :=
    rescale_smul scale_ne_zero predict weights
  simp only [GET_RESIDUAL, ContinuousLinearMap.coe_coe, same_output]

/-- **Flatter by `scale²`.** The curvature of the loss along any direction is
divided by `scale²`. -/
theorem norm_rescale_sq
    (scale : ℝ)
    (predict : Weights →L[ℝ] Outputs)
    (move : Weights) :
    let rescaled_size_sq := ‖RESCALE scale predict move‖ ^ 2
    let size_sq          := ‖predict move‖ ^ 2 / scale ^ 2  -- the output is divided by `scale`, so its square by `scale²`
    rescaled_size_sq = size_sq := by
  unfold_named_pieces
  rw [RESCALE, smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    inv_pow]
  ring

/-- The distances to the fits are all multiplied by `|scale|`. -/
theorem fitDistances_rescale
    {scale : ℝ}
    (scale_ne_zero : scale ≠ 0)
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (start_weights : Weights) :
    let rescaled_predict : LinearPredictor Weights Outputs :=
      RESCALE scale predict
    let linear_predict : LinearPredictor Weights Outputs := predict
    let rescaled_distances :=
      GET_FIT_DISTANCES rescaled_predict labels (scale • start_weights)
    let scaled_distances   :=
      |scale| • GET_FIT_DISTANCES linear_predict labels start_weights
    rescaled_distances = scaled_distances := by
  unfold_named_pieces
  ext distance
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨other_weights, other_weights_fit, rfl⟩
    -- Going back to the old units: divide the rescaled fit by `scale`.
    refine ⟨‖scale⁻¹ • other_weights - start_weights‖,
      ⟨scale⁻¹ • other_weights, ?_, rfl⟩, ?_⟩
    · have fit_rescaled : RESCALE scale predict other_weights = labels :=
        other_weights_fit
      rw [← fit_rescaled, RESCALE, smul_apply, ContinuousLinearMap.coe_coe,
        map_smul]
    · have difference_scaled :
          scale⁻¹ • other_weights - start_weights
            = scale⁻¹ • (other_weights - scale • start_weights) := by
        rw [smul_sub, inv_smul_smul₀ scale_ne_zero]
      rw [difference_scaled, norm_smul, norm_inv, Real.norm_eq_abs,
        smul_eq_mul, mul_inv_cancel_left₀ (abs_ne_zero.mpr scale_ne_zero)]
  · rintro ⟨_, ⟨weights, weights_fit, rfl⟩, rfl⟩
    refine ⟨scale • weights, ?_, ?_⟩
    · have fit_original : predict weights = labels := weights_fit
      rw [ContinuousLinearMap.coe_coe,
        (rescale_smul scale_ne_zero predict weights :
          RESCALE scale predict (scale • weights) = predict weights),
        fit_original]
    · rw [← smul_sub, norm_smul, Real.norm_eq_abs, smul_eq_mul]

/-- **Farther by `|scale|`.** The nearest fit of the rescaled model is
`|scale|` times as far from the start. -/
theorem travel_rescale
    {scale : ℝ}
    (scale_ne_zero : scale ≠ 0)
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (start_weights : Weights) :
    let rescaled_predict : LinearPredictor Weights Outputs :=
      RESCALE scale predict
    let linear_predict : LinearPredictor Weights Outputs := predict
    let rescaled_travel :=
      GET_TRAVEL rescaled_predict labels (scale • start_weights)
    let travel          :=
      |scale| * GET_TRAVEL linear_predict labels start_weights
    rescaled_travel = travel := by
  unfold_named_pieces
  have distances_scaled :
      GET_FIT_DISTANCES (RESCALE scale predict : Weights →ₗ[ℝ] Outputs) labels
          (scale • start_weights)
        = |scale| • GET_FIT_DISTANCES (predict : Weights →ₗ[ℝ] Outputs) labels
            start_weights :=
    fitDistances_rescale scale_ne_zero predict labels start_weights
  rw [GET_TRAVEL, GET_TRAVEL, distances_scaled,
    Real.sInf_smul_of_nonneg (abs_nonneg scale), smul_eq_mul]

/-- **Flatter is farther.** Rescaling by `scale` keeps the error, divides the
curvature of the loss by `scale²`, and multiplies the distance to the nearest
fit by `|scale|`. -/
theorem flatter_is_farther
    {scale : ℝ}
    (scale_ne_zero : scale ≠ 0)
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (start_weights : Weights) :
    let rescaled_predict : LinearPredictor Weights Outputs :=
      RESCALE scale predict
    let linear_predict : LinearPredictor Weights Outputs := predict
    let error_is_kept :=
      GET_RESIDUAL rescaled_predict labels (scale • start_weights)
        = GET_RESIDUAL linear_predict labels start_weights
    let loss_is_flatter := ∀ move : Weights,
      ‖RESCALE scale predict move‖ ^ 2 = ‖predict move‖ ^ 2 / scale ^ 2
    let fit_is_farther :=
      GET_TRAVEL rescaled_predict labels (scale • start_weights)
        = |scale| * GET_TRAVEL linear_predict labels start_weights
    error_is_kept ∧ loss_is_flatter ∧ fit_is_farther := by
  unfold_named_pieces
  exact ⟨residual_rescale scale_ne_zero predict labels start_weights,
    norm_rescale_sq scale predict,
    travel_rescale scale_ne_zero predict labels start_weights⟩

end Units

/-! ### The kernel, the gradient step, and what does not change -/

section Training

open ContinuousLinearMap

variable {Weights Outputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]

/-- The adjoint of the rescaled model. -/
theorem adjoint_rescale
    (scale : ℝ)
    (predict : Weights →L[ℝ] Outputs) :
    let rescaled_adjoint := adjoint (RESCALE scale predict)
    let scaled_adjoint   := scale⁻¹ • adjoint predict
    rescaled_adjoint = scaled_adjoint := by
  unfold_named_pieces
  rw [RESCALE, map_smulₛₗ, conj_trivial]

/-- **The kernel is weaker by `scale²`.** -/
theorem kernel_rescale
    (scale : ℝ)
    (predict : Weights →L[ℝ] Outputs)
    (vector : Outputs) :
    let rescaled_kernel :=
      RESCALE scale predict (adjoint (RESCALE scale predict) vector)
    let weaker_kernel   :=
      (scale ^ 2)⁻¹ • predict (adjoint predict vector)  -- `scale⁻¹` once for the model, once for its adjoint
    rescaled_kernel = weaker_kernel := by
  unfold_named_pieces
  have adjoint_scaled :
      adjoint (RESCALE scale predict) = scale⁻¹ • adjoint predict :=
    adjoint_rescale scale predict
  rw [adjoint_scaled, RESCALE, smul_apply, smul_apply, map_smul, smul_smul,
    ← mul_inv, ← sq]

/-- **Rescaling is a change of step size.** A gradient step of the rescaled
model with step size `learning_rate` is a step of the model with step size
`learning_rate / scale²`. -/
theorem gradientStep_rescale
    {scale : ℝ}
    (scale_ne_zero : scale ≠ 0)
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (weights : Weights) :
    let rescaled_step :=
      TAKE_GRADIENT_STEP (RESCALE scale predict) labels learning_rate
        (scale • weights)
    let original_step :=
      scale • TAKE_GRADIENT_STEP predict labels (learning_rate / scale ^ 2)
        weights
    rescaled_step = original_step := by
  unfold_named_pieces
  have step_factor :
      learning_rate * scale⁻¹ = scale * (learning_rate / scale ^ 2) := by
    field_simp
  have residual_same :
      GET_RESIDUAL (RESCALE scale predict : Weights →ₗ[ℝ] Outputs) labels
          (scale • weights)
        = GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights :=
    residual_rescale scale_ne_zero predict labels weights
  have adjoint_scaled :
      adjoint (RESCALE scale predict) = scale⁻¹ • adjoint predict :=
    adjoint_rescale scale predict
  rw [TAKE_GRADIENT_STEP, TAKE_GRADIENT_STEP, residual_same, adjoint_scaled,
    smul_apply, smul_add, smul_smul, smul_smul, step_factor]

/-- **What does not change.** If the residual lies along a direction of
strength `kernel_strength`, then strength times travel squared is the error
squared. Flat means far and sharp means near. -/
theorem strength_mul_travel_sq
    (predict : Weights →L[ℝ] Outputs)
    (kernel_inverse : Outputs → Outputs)
    (kernel_inverse_works : ∀ vector,
      predict (adjoint predict (kernel_inverse vector)) = vector)
    {kernel_strength : ℝ}
    (kernel_strength_pos : 0 < kernel_strength)
    (labels : Outputs)
    (start_weights : Weights)
    (residual_is_stretched :
      predict (adjoint predict
        (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
          start_weights))
        = kernel_strength
          • GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
              start_weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let travel          := GET_TRAVEL linear_predict labels start_weights
    let residual_size   :=
      ‖GET_RESIDUAL linear_predict labels start_weights‖
    let strength_times_travel_sq := kernel_strength * travel ^ 2
    let error_sq                 := residual_size ^ 2
    strength_times_travel_sq = error_sq := by
  unfold_named_pieces
  have travel_exact :
      GET_TRAVEL (predict : Weights →ₗ[ℝ] Outputs) labels start_weights
        = ‖GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
            start_weights‖ / √kernel_strength :=
    travel_eq_of_eigen predict kernel_inverse kernel_inverse_works
      kernel_strength_pos labels start_weights residual_is_stretched
  -- Travel is the error over `√kernel_strength`; squaring cancels the root.
  rw [travel_exact, div_pow, Real.sq_sqrt kernel_strength_pos.le]
  field_simp

end Training

end SquigglyLine
