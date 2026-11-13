/-
Double descent, as the travel peak.

Two inequalities connect the test-error peak of double descent to the
distance from the start to the nearest fit.

* `exists_fit_near_start`: there is a fit whose output on any feature vector
  differs from the output at the start by at most the size of that vector
  times the travel. A fit that is near the start is tame everywhere.
* `travel_le_of_le_kernel`: if the kernel is at least `kernel_floor` in every
  direction, the travel is at most the size of the residual divided by
  `√kernel_floor`. The travel can be large only where the kernel has a weak
  direction, which is what happens when the model has barely enough
  parameters to fit.

That the test error does peak there is measured (`scripts/double_descent.py`),
not proved.

* `abs_inner_sub_le`                  an output moves by at most the feature
                                      length times the distance moved;
* `exists_fit_near_start`             a fit near the start is tame;
* `travel_le_of_le_kernel`            a strong kernel means a short travel;
* `kernel_inner_comm`                 the kernel is symmetric;
* `not_exists_fit_of_kernel_eq_zero`  strength zero: out of reach;
* `travel_eq_of_eigen`                strength `strength`: the exact price;
* `le_travel_of_eigen_le`             the weaker the direction, the further
                                      the fit;
* `tightFeatures_innerSL`             one training point has tight features;
* `travel_one_point`                  one training point: travel is error over
                                      feature length.
-/
import SquigglyLine.Networks.Kernel

namespace SquigglyLine

open ContinuousLinearMap

variable {Weights Outputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]

omit [CompleteSpace Weights] in
/-- The output on a feature vector moves by at most its length times the
distance moved in parameter space. -/
theorem abs_inner_sub_le
    (features : Weights)
    (weights : Weights)
    (start_weights : Weights) :
    let output_here    := inner ℝ features weights
    let output_start   := inner ℝ features start_weights
    let output_change  := |output_here - output_start|
    let distance_moved := ‖weights - start_weights‖
    output_change ≤ ‖features‖ * distance_moved := by
  unfold_named_pieces
  rw [← inner_sub_right]
  exact abs_real_inner_le_norm _ _

/-- **A fit near the start is tame everywhere.** There is a fit whose output on
every feature vector is within its length times the travel of the output at the
start. -/
theorem exists_fit_near_start
    (predict : Weights →L[ℝ] Outputs)
    (kernel_inverse : Outputs → Outputs)
    (kernel_inverse_works : ∀ vector,
      predict (adjoint predict (kernel_inverse vector)) = vector)
    (labels : Outputs)
    (start_weights : Weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let travel := GET_TRAVEL linear_predict labels start_weights
    ∃ weights : Weights,
      let fits_the_data := predict weights = labels
      let is_tame       := ∀ features : Weights,
        |inner ℝ features weights - inner ℝ features start_weights|
          ≤ ‖features‖ * travel
      fits_the_data ∧ is_tame := by
  unfold_named_pieces
  -- The fit is the start plus the move `A† K⁻¹ residual`.
  refine ⟨start_weights + adjoint predict (kernel_inverse
    (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels start_weights)),
    ?_, fun features => ?_⟩
  · rw [map_add, kernel_inverse_works]
    simp [GET_RESIDUAL]
  · rw [travel_eq_norm_of_kernelInverse predict kernel_inverse
      kernel_inverse_works]
    calc |inner ℝ features (start_weights + adjoint predict (kernel_inverse
            (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
              start_weights))) - inner ℝ features start_weights|
        ≤ ‖features‖ * ‖start_weights + adjoint predict (kernel_inverse
            (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
              start_weights)) - start_weights‖ :=
          abs_inner_sub_le _ _ _
      _ = ‖features‖ * ‖adjoint predict (kernel_inverse
            (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
              start_weights))‖ := by
          rw [add_sub_cancel_left]

/-- **The travel is large only where the kernel is weak.** If the kernel is at
least `kernel_floor` in every direction, the travel is at most the size of the
residual divided by `√kernel_floor`. -/
theorem travel_le_of_le_kernel
    (predict : Weights →L[ℝ] Outputs)
    (kernel_inverse : Outputs → Outputs)
    (kernel_inverse_works : ∀ vector,
      predict (adjoint predict (kernel_inverse vector)) = vector)
    {kernel_floor : ℝ}
    (kernel_floor_pos : 0 < kernel_floor)
    (kernel_above_floor : ∀ vector,
      kernel_floor * ‖vector‖ ^ 2
        ≤ inner ℝ (predict (adjoint predict vector)) vector)
    (labels : Outputs)
    (start_weights : Weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let travel        := GET_TRAVEL linear_predict labels start_weights
    let residual_size :=
      ‖GET_RESIDUAL linear_predict labels start_weights‖
    let floor_root    := √kernel_floor  -- the exchange rate of the weakest direction
    travel ≤ residual_size / floor_root := by
  unfold_named_pieces
  obtain ⟨residual, residual_def⟩ : ∃ residual,
      residual = GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
        start_weights :=
    ⟨_, rfl⟩
  rw [travel_eq_norm_of_kernelInverse predict kernel_inverse
    kernel_inverse_works, ← residual_def]
  have squared_eq : ‖adjoint predict (kernel_inverse residual)‖ ^ 2
      = inner ℝ (kernel_inverse residual) residual :=
    norm_adjoint_kernelInverse_sq predict kernel_inverse
      kernel_inverse_works residual
  have kernel_inverse_residual_works :=
    kernel_inverse_works residual
  obtain ⟨preimage, preimage_def⟩ : ∃ preimage,
      preimage = kernel_inverse residual := ⟨_, rfl⟩
  rw [← preimage_def] at squared_eq kernel_inverse_residual_works ⊢
  have floor_bound : kernel_floor * ‖preimage‖ ^ 2
      ≤ ‖residual‖ * ‖preimage‖ :=
    calc kernel_floor * ‖preimage‖ ^ 2
        ≤ inner ℝ (predict (adjoint predict preimage)) preimage :=
          kernel_above_floor preimage
      _ = inner ℝ residual preimage := by
          rw [kernel_inverse_residual_works]
      _ ≤ ‖residual‖ * ‖preimage‖ := real_inner_le_norm _ _
  have linear_bound : kernel_floor * ‖preimage‖ ≤ ‖residual‖ := by
    rcases eq_or_lt_of_le (norm_nonneg preimage) with zero | positive
    · rw [← zero, mul_zero]
      exact norm_nonneg _
    · have times_preimage : ‖preimage‖ * (kernel_floor * ‖preimage‖)
          ≤ ‖preimage‖ * ‖residual‖ := by nlinarith [floor_bound]
      exact le_of_mul_le_mul_left times_preimage positive
  have pullback_sq_bound :
      ‖adjoint predict preimage‖ ^ 2 ≤ ‖residual‖ ^ 2 / kernel_floor := by
    rw [squared_eq, le_div_iff₀ kernel_floor_pos]
    calc inner ℝ preimage residual * kernel_floor
        ≤ ‖preimage‖ * ‖residual‖ * kernel_floor :=
          mul_le_mul_of_nonneg_right (real_inner_le_norm _ _)
            kernel_floor_pos.le
      _ = kernel_floor * ‖preimage‖ * ‖residual‖ := by ring
      _ ≤ ‖residual‖ * ‖residual‖ :=
          mul_le_mul_of_nonneg_right linear_bound (norm_nonneg _)
      _ = ‖residual‖ ^ 2 := by ring
  -- Take square roots on both sides.
  calc ‖adjoint predict preimage‖
      = √(‖adjoint predict preimage‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(‖residual‖ ^ 2 / kernel_floor) :=
        Real.sqrt_le_sqrt pullback_sq_bound
    _ = ‖residual‖ / √kernel_floor := by
        rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-! ### The peak, exactly: one direction of the labels

Follow one direction `residual` of the labels that the kernel stretches by
`strength`. `strength = 0`: out of reach. `strength` small: reachable at a
huge price. `strength` large: cheap. -/

/-- The kernel is symmetric. -/
theorem kernel_inner_comm
    (predict : Weights →L[ℝ] Outputs)
    (vector : Outputs)
    (other_vector : Outputs) :
    let left_form  := inner ℝ (predict (adjoint predict vector)) other_vector
    let right_form := inner ℝ vector (predict (adjoint predict other_vector))
    left_form = right_form := by
  unfold_named_pieces
  exact (adjoint_inner_right predict (adjoint predict vector)
    other_vector).symm.trans
    (adjoint_inner_left predict (adjoint predict other_vector) vector)

/-- **Strength zero: out of reach.** If the kernel sends a direction to zero,
no change of the parameters produces it. The model cannot fit that part of the
labels. -/
theorem not_exists_fit_of_kernel_eq_zero
    (predict : Weights →L[ℝ] Outputs)
    {residual : Outputs}
    (residual_ne_zero : residual ≠ 0)
    (kernel_kills_residual : predict (adjoint predict residual) = 0) :
    let can_be_produced := ∃ step : Weights, predict step = residual
    ¬ can_be_produced := by
  unfold_named_pieces
  rintro ⟨step, step_gives_residual⟩
  have pullback_zero : adjoint predict residual = 0 := by
    have pullback_sq_zero : ‖adjoint predict residual‖ ^ 2 = 0 := by
      rw [← real_inner_self_eq_norm_sq, adjoint_inner_left,
        kernel_kills_residual, inner_zero_right]
    simpa using pullback_sq_zero
  have residual_sq_zero : ‖residual‖ ^ 2 = 0 := by
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 2 [← step_gives_residual]
    rw [← adjoint_inner_left, pullback_zero, inner_zero_left]
  exact residual_ne_zero (by simpa using residual_sq_zero)

/-- **Strength `strength`: the exact price.** If the residual lies along a
direction that the kernel stretches by `strength > 0`, the travel is exactly
the size of the residual divided by `√strength`. -/
theorem travel_eq_of_eigen
    (predict : Weights →L[ℝ] Outputs)
    (kernel_inverse : Outputs → Outputs)
    (kernel_inverse_works : ∀ vector,
      predict (adjoint predict (kernel_inverse vector)) = vector)
    {strength : ℝ}
    (strength_pos : 0 < strength)
    (labels : Outputs)
    (start_weights : Weights)
    (residual_is_stretched :
      predict (adjoint predict
        (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
          start_weights))
        = strength
          • GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
              start_weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let travel        := GET_TRAVEL linear_predict labels start_weights
    let residual_size :=
      ‖GET_RESIDUAL linear_predict labels start_weights‖
    let price         := √strength  -- travel is residual over `√strength`
    travel = residual_size / price := by
  unfold_named_pieces
  obtain ⟨residual, residual_def⟩ : ∃ residual,
      residual = GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
        start_weights :=
    ⟨_, rfl⟩
  rw [travel_eq_norm_of_kernelInverse predict kernel_inverse
    kernel_inverse_works, ← residual_def]
  rw [← residual_def] at residual_is_stretched
  have kernel_form_eq :
      inner ℝ (predict (adjoint predict (kernel_inverse residual))) residual
        = inner ℝ (kernel_inverse residual)
            (predict (adjoint predict residual)) :=
    kernel_inner_comm predict (kernel_inverse residual) residual
  have stretched_form : strength * inner ℝ (kernel_inverse residual) residual
      = ‖residual‖ ^ 2 := by
    rw [← real_inner_smul_right, ← residual_is_stretched, ← kernel_form_eq,
      kernel_inverse_works residual, real_inner_self_eq_norm_sq]
  have pullback_sq : ‖adjoint predict (kernel_inverse residual)‖ ^ 2
      = ‖residual‖ ^ 2 / strength := by
    have squared_eq : ‖adjoint predict (kernel_inverse residual)‖ ^ 2
        = inner ℝ (kernel_inverse residual) residual :=
      norm_adjoint_kernelInverse_sq predict kernel_inverse
        kernel_inverse_works residual
    rw [squared_eq, eq_div_iff strength_pos.ne', mul_comm]
    exact stretched_form
  calc ‖adjoint predict (kernel_inverse residual)‖
      = √(‖adjoint predict (kernel_inverse residual)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = √(‖residual‖ ^ 2 / strength) := by rw [pullback_sq]
    _ = ‖residual‖ / √strength := by
        rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- **The peak.** The weaker the direction, the further the fit: if the kernel
stretches the residual's direction by at most `tolerance ^ 2`, the travel is at
least the size of the residual divided by `tolerance`. As `tolerance` goes to
zero this grows without bound. -/
theorem le_travel_of_eigen_le
    (predict : Weights →L[ℝ] Outputs)
    (kernel_inverse : Outputs → Outputs)
    (kernel_inverse_works : ∀ vector,
      predict (adjoint predict (kernel_inverse vector)) = vector)
    {strength tolerance : ℝ}
    (strength_pos : 0 < strength)
    (tolerance_pos : 0 < tolerance)
    (strength_le_square : strength ≤ tolerance ^ 2)
    (labels : Outputs)
    (start_weights : Weights)
    (residual_is_stretched :
      predict (adjoint predict
        (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
          start_weights))
        = strength
          • GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
              start_weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let travel        := GET_TRAVEL linear_predict labels start_weights
    let residual_size :=
      ‖GET_RESIDUAL linear_predict labels start_weights‖
    residual_size / tolerance ≤ travel := by
  unfold_named_pieces
  have travel_exact :
      GET_TRAVEL (predict : Weights →ₗ[ℝ] Outputs) labels start_weights
        = ‖GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
            start_weights‖ / √strength :=
    travel_eq_of_eigen predict kernel_inverse kernel_inverse_works
      strength_pos labels start_weights residual_is_stretched
  rw [travel_exact]
  refine div_le_div_of_nonneg_left (norm_nonneg _)
    (Real.sqrt_pos.mpr strength_pos) ?_
  calc √strength ≤ √(tolerance ^ 2) := Real.sqrt_le_sqrt strength_le_square
    _ = tolerance := Real.sqrt_sq tolerance_pos.le

/-! ### The smallest example: one training point -/

/-- With one training point and feature vector `feature_vector`, the kernel is
the squared length of `feature_vector`. Adding features can only make it
larger. -/
theorem tightFeatures_innerSL
    (feature_vector : Weights) :
    let one_point_predict := innerSL ℝ feature_vector
    let squared_length    := ‖feature_vector‖ ^ 2  -- the kernel of one point is a 1 × 1 matrix
    HAS_TIGHT_FEATURES one_point_predict squared_length := by
  unfold_named_pieces
  intro scalar
  rw [adjoint_innerSL_apply]
  simp [mul_comm]

/-- **One training point.** The distance to the nearest fit is the error
divided by the length of the feature vector. A short feature vector means a
distant fit. -/
theorem travel_one_point
    {feature_vector : Weights}
    (feature_vector_ne_zero : feature_vector ≠ 0)
    (label : ℝ)
    (start_weights : Weights) :
    let linear_predict : LinearPredictor Weights ℝ := innerSL ℝ feature_vector
    let travel         := GET_TRAVEL linear_predict label start_weights
    let error          := |label - inner ℝ feature_vector start_weights|
    let feature_length := ‖feature_vector‖
    travel = error / feature_length := by
  unfold_named_pieces
  have tight_features : HAS_TIGHT_FEATURES (innerSL ℝ feature_vector)
      (‖feature_vector‖ ^ 2) :=
    tightFeatures_innerSL feature_vector
  rw [tight_features.travel_eq
      (pow_pos (norm_pos_iff.mpr feature_vector_ne_zero) 2) label
      start_weights,
    Real.sqrt_sq (norm_nonneg feature_vector)]
  simp [GET_RESIDUAL, Real.norm_eq_abs]

end SquigglyLine
