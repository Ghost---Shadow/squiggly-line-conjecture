/-
Parameter distance is loss, at an exchange rate.

Say the features are tight with constant `squared_length` when
`predict (adjoint predict vector) = squared_length • vector`: seen from the
data side they are orthogonal, each with squared length `squared_length`. A
Fourier series with `m` terms on `n` well-spread points is nearly tight with
`squared_length = m + 1`.

Then the distance in parameter space from any start to the nearest fit is
exactly the size of the residual divided by `√squared_length`:

    travel = ‖residual‖ / √squared_length

So the loss and the parameter distance are one quantity in two units, and
adding parameters changes only the rate between them. With
`squared_length = 1`, which is `n` orthonormal features for `n` points, the
two are equal.

* `HAS_TIGHT_FEATURES`        the features are orthogonal on the data side,
                              each with squared length `squared_length`;
* `norm_adjoint_sq`           the adjoint scales squared lengths by
                              `squared_length`;
* `norm_map_sq_le`            a step changes the outputs by at most
                              `√squared_length` times its length;
* `travel_eq`                 the exchange rate: travel is the residual size
                              over `√squared_length`;
* `travel_eq_norm_residual`   with `squared_length = 1` the two are equal.
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import SquigglyLine.Networks.LinearModel

namespace SquigglyLine

open ContinuousLinearMap

variable {Weights Outputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]
  {predict : Weights →L[ℝ] Outputs} {squared_length : ℝ}

/-- The features are orthogonal on the data side, each with squared length
`squared_length`. -/
def HAS_TIGHT_FEATURES
    (predict : Weights →L[ℝ] Outputs)
    (squared_length : ℝ) : Prop :=
  ∀ vector, predict (adjoint predict vector) = squared_length • vector

namespace HAS_TIGHT_FEATURES

/-- Pulling a vector back to weight space scales its squared length by
`squared_length`. -/
theorem norm_adjoint_sq
    (features_are_tight : HAS_TIGHT_FEATURES predict squared_length)
    (vector : Outputs) :
    let pullback_size := ‖adjoint predict vector‖ ^ 2
    let scaled_size   := squared_length * ‖vector‖ ^ 2
    pullback_size = scaled_size := by
  unfold_named_pieces
  rw [← real_inner_self_eq_norm_sq, adjoint_inner_left,
    features_are_tight vector, real_inner_smul_right,
    real_inner_self_eq_norm_sq]

/-- A move of size `‖step‖` in parameter space changes the outputs by at most
`√squared_length ‖step‖`. -/
theorem norm_map_sq_le
    (features_are_tight : HAS_TIGHT_FEATURES predict squared_length)
    (squared_length_pos : 0 < squared_length)
    (step : Weights) :
    let output_change := ‖predict step‖ ^ 2
    let step_bound    := squared_length * ‖step‖ ^ 2
    output_change ≤ step_bound := by
  unfold_named_pieces
  have output_le_pullback :
      ‖predict step‖ ^ 2 ≤ ‖adjoint predict (predict step)‖ * ‖step‖ := by
    rw [← real_inner_self_eq_norm_sq, ← adjoint_inner_left]
    exact real_inner_le_norm _ _
  have pullback_sq : ‖adjoint predict (predict step)‖ ^ 2
      = squared_length * ‖predict step‖ ^ 2 :=
    features_are_tight.norm_adjoint_sq _
  rcases eq_or_lt_of_le (sq_nonneg ‖predict step‖) with zero | positive
  · rw [← zero]
    positivity
  · -- Square both sides of `output_le_pullback`, then cancel one factor.
    have squared_bound : ‖predict step‖ ^ 2 * ‖predict step‖ ^ 2
        ≤ ‖predict step‖ ^ 2 * (squared_length * ‖step‖ ^ 2) :=
      calc ‖predict step‖ ^ 2 * ‖predict step‖ ^ 2
          = (‖predict step‖ ^ 2) ^ 2 := (sq _).symm
        _ ≤ (‖adjoint predict (predict step)‖ * ‖step‖) ^ 2 :=
          pow_le_pow_left₀ (sq_nonneg _) output_le_pullback 2
        _ = ‖predict step‖ ^ 2 * (squared_length * ‖step‖ ^ 2) := by
          rw [mul_pow, pullback_sq]
          ring
    exact le_of_mul_le_mul_left squared_bound positive

/-- **The exchange rate.** With tight features, the distance in parameter
space from the start to the nearest fit is the size of the residual divided by
`√squared_length`. -/
theorem travel_eq
    (features_are_tight : HAS_TIGHT_FEATURES predict squared_length)
    (squared_length_pos : 0 < squared_length)
    (labels : Outputs)
    (start_weights : Weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let travel        := GET_TRAVEL linear_predict labels start_weights
    let residual_size :=
      ‖GET_RESIDUAL linear_predict labels start_weights‖
    let exchange_rate := √squared_length  -- parameter distance per unit of residual, inverted
    travel = residual_size / exchange_rate := by
  unfold_named_pieces
  set residual := GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
    start_weights with residual_def
  have root_pos : 0 < √squared_length := Real.sqrt_pos.mpr squared_length_pos
  rw [GET_TRAVEL]
  refine IsLeast.csInf_eq ⟨?_, ?_⟩
  · -- Move from the start along the features by the amount that cancels the
    -- residual. This reaches a fit.
    refine ⟨start_weights + squared_length⁻¹ • adjoint predict residual,
      ?_, ?_⟩
    · simp only [ContinuousLinearMap.coe_coe, map_add, map_smul,
        features_are_tight residual, smul_smul,
        inv_mul_cancel₀ squared_length_pos.ne', one_smul]
      simp [residual_def, GET_RESIDUAL]
    · have pullback_size :
          ‖adjoint predict residual‖ = √squared_length * ‖residual‖ := by
        rw [← Real.sqrt_sq (norm_nonneg (adjoint predict residual)),
          features_are_tight.norm_adjoint_sq residual,
          Real.sqrt_mul squared_length_pos.le,
          Real.sqrt_sq (norm_nonneg residual)]
      rw [add_sub_cancel_left, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr squared_length_pos.le),
        pullback_size, eq_div_iff root_pos.ne',
        show squared_length⁻¹ * (√squared_length * ‖residual‖)
            * √squared_length
          = squared_length⁻¹ * (√squared_length * √squared_length)
            * ‖residual‖ by ring,
        Real.mul_self_sqrt squared_length_pos.le,
        inv_mul_cancel₀ squared_length_pos.ne', one_mul]
  · -- Every fit is at least this far: it must cancel the same residual.
    rintro distance ⟨weights, weights_fit, rfl⟩
    have step_gives_residual :
        predict (weights - start_weights) = residual := by
      have predict_weights : predict weights = labels := weights_fit
      simp [residual_def, GET_RESIDUAL, map_sub, predict_weights]
    have step_bound : ‖predict (weights - start_weights)‖ ^ 2
        ≤ squared_length * ‖weights - start_weights‖ ^ 2 :=
      features_are_tight.norm_map_sq_le squared_length_pos
        (weights - start_weights)
    rw [step_gives_residual] at step_bound
    rw [div_le_iff₀ root_pos]
    calc ‖residual‖
        = √(‖residual‖ ^ 2) := (Real.sqrt_sq (norm_nonneg residual)).symm
      _ ≤ √(squared_length * ‖weights - start_weights‖ ^ 2) :=
        Real.sqrt_le_sqrt step_bound
      _ = ‖weights - start_weights‖ * √squared_length := by
          rw [Real.sqrt_mul squared_length_pos.le,
            Real.sqrt_sq (norm_nonneg _), mul_comm]

/-- **Parameter space is data space.** With orthonormal features, the distance
to the nearest fit is exactly the size of the residual. -/
theorem travel_eq_norm_residual
    (features_are_orthonormal : HAS_TIGHT_FEATURES predict 1)
    (labels : Outputs)
    (start_weights : Weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let travel        := GET_TRAVEL linear_predict labels start_weights
    let residual_size :=
      ‖GET_RESIDUAL linear_predict labels start_weights‖
    travel = residual_size := by
  unfold_named_pieces
  simpa using features_are_orthonormal.travel_eq one_pos labels start_weights

end HAS_TIGHT_FEATURES

end SquigglyLine
