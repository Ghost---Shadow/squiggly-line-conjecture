/-
Benign overfitting: fitting the noise without paying for it.

What is left to fit splits into a signal `signal` and a noise `noise`, along
kernel directions of strengths `signal_strength` and `noise_strength`.
`GET_SPLIT_FIT` is the fit gradient descent heads for.

* `splitFit_fits`, `splitFit_is_nearest` : it fits signal and noise exactly,
  and no fit is nearer to the start.
* `inner_splitFit` : at a new input the answer moves by the signal's overlap
  divided by `signal_strength` plus the noise's overlap divided by
  `noise_strength`.
* `abs_noise_damage_le` : with junk features of strength `junk_strength` in
  every direction, the noise term is at most the overlap divided by
  `junk_strength`.
* `abs_signal_loss_le` : and the signal term changes by at most the fraction
  `junk_strength / signal_strength` of itself.
* `benign_overfitting` : the three together.

Definition: `GET_SPLIT_FIT`. Helper: `abs_div_add_le`.
-/
import SquigglyLine.Supporting.Training.LeastAction
import SquigglyLine.Supporting.NewInputs.Pruning

namespace SquigglyLine

open ContinuousLinearMap

/-! ### The two terms -/

section Terms

/-- **The damage is capped by the junk.** A noise direction of any strength
`noise_strength ≥ 0`, after junk features add `junk_strength`, moves a new
answer by at most the overlap over `junk_strength`. -/
theorem abs_div_add_le
    {overlap overlap_bound noise_strength junk_strength : ℝ}
    (overlap_in_bound : |overlap| ≤ overlap_bound)
    (noise_strength_nonneg : 0 ≤ noise_strength)
    (junk_strength_pos : 0 < junk_strength) :
    let damage     := |overlap / (noise_strength + junk_strength)|
    let damage_cap := overlap_bound / junk_strength
    damage ≤ damage_cap := by
  unfold_named_pieces
  have total_strength_pos : 0 < noise_strength + junk_strength := by linarith
  -- Dividing by something at least as big as the junk can only shrink it.
  calc |overlap / (noise_strength + junk_strength)|
      = |overlap| / (noise_strength + junk_strength) := by
        rw [abs_div, abs_of_pos total_strength_pos]
    _ ≤ |overlap| / junk_strength :=
        div_le_div_of_nonneg_left (abs_nonneg _) junk_strength_pos
          (by linarith)
    _ ≤ overlap_bound / junk_strength := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right overlap_in_bound
          (inv_nonneg.mpr junk_strength_pos.le)

/-- **The signal is nearly untouched.** Adding `junk_strength` to a strong
direction changes its term by at most the fraction
`junk_strength / signal_strength` of itself. -/
theorem abs_signal_loss_le
    (overlap : ℝ)
    {signal_strength junk_strength : ℝ}
    (signal_strength_pos : 0 < signal_strength)
    (junk_strength_nonneg : 0 ≤ junk_strength) :
    let signal_term  := overlap / signal_strength
    let changed_term := overlap / (signal_strength + junk_strength)
    let loss         := |signal_term - changed_term|
    let allowed_loss := |signal_term| * (junk_strength / signal_strength)  -- the fraction of the term that is lost
    loss ≤ allowed_loss := by
  unfold_named_pieces
  have total_strength_pos : 0 < signal_strength + junk_strength := by linarith
  -- The difference of the two terms, written as the term times a fraction.
  have difference_eq :
      overlap / signal_strength - overlap / (signal_strength + junk_strength)
        = overlap / signal_strength
          * (junk_strength / (signal_strength + junk_strength)) := by
    field_simp
    ring
  rw [difference_eq, abs_mul,
    abs_of_nonneg (div_nonneg junk_strength_nonneg total_strength_pos.le)]
  exact mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_left junk_strength_nonneg signal_strength_pos
      (by linarith))
    (abs_nonneg _)

end Terms

/-! ### The fit that swallows the noise -/

section Fit

variable {Weights Outputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]

/-- The fit that gradient descent heads for when the residual is a signal
`signal` plus a noise `noise`, along kernel directions of strengths
`signal_strength` and `noise_strength`.
Python: `start_weights + adjoint(whole_predict)(signal / signal_strength
+ noise / noise_strength)`. -/
noncomputable def GET_SPLIT_FIT
    (whole_predict : Weights →L[ℝ] Outputs)
    (start_weights : Weights)
    (signal : Outputs)
    (noise : Outputs)
    (signal_strength : ℝ)
    (noise_strength : ℝ) : Weights :=
  start_weights
    + adjoint whole_predict
      (signal_strength⁻¹ • signal + noise_strength⁻¹ • noise)

/-- **It fits the signal and the noise exactly.** -/
theorem splitFit_fits
    (whole_predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (start_weights : Weights)
    {signal noise : Outputs}
    {signal_strength noise_strength : ℝ}
    (signal_strength_ne_zero : signal_strength ≠ 0)
    (noise_strength_ne_zero : noise_strength ≠ 0)
    (signal_is_eigen :
      whole_predict (adjoint whole_predict signal)
        = signal_strength • signal)
    (noise_is_eigen :
      whole_predict (adjoint whole_predict noise)
        = noise_strength • noise)
    (residual_splits :
      GET_RESIDUAL (whole_predict : Weights →ₗ[ℝ] Outputs) labels
        start_weights = signal + noise) :
    let fit :=
      GET_SPLIT_FIT whole_predict start_weights signal noise signal_strength
        noise_strength
    let fit_outputs := whole_predict fit
    fit_outputs = labels := by
  unfold_named_pieces
  simp only [GET_SPLIT_FIT, map_add, map_smul, signal_is_eigen,
    noise_is_eigen, smul_smul, inv_mul_cancel₀ signal_strength_ne_zero,
    inv_mul_cancel₀ noise_strength_ne_zero, one_smul]
  rw [← residual_splits]
  simp [GET_RESIDUAL]

/-- **No fit is nearer.** -/
theorem splitFit_is_nearest
    (whole_predict : Weights →L[ℝ] Outputs)
    {labels : Outputs}
    (start_weights : Weights)
    (signal : Outputs)
    (noise : Outputs)
    (signal_strength : ℝ)
    (noise_strength : ℝ)
    (fit_fits :
      whole_predict
          (GET_SPLIT_FIT whole_predict start_weights signal noise
            signal_strength noise_strength)
        = labels)
    {other_weights : Weights}
    (other_fits : whole_predict other_weights = labels) :
    let fit :=
      GET_SPLIT_FIT whole_predict start_weights signal noise signal_strength
        noise_strength
    let fit_distance   := ‖fit - start_weights‖
    let other_distance := ‖other_weights - start_weights‖
    fit_distance ≤ other_distance := by
  unfold_named_pieces
  exact norm_sub_le_of_fit_along_features whole_predict rfl fit_fits
    other_fits

/-- **What the fit does to a new input.** The answer at `query_features`
moves by the signal's overlap with the test row divided by `signal_strength`,
plus the noise's overlap divided by `noise_strength`. -/
theorem inner_splitFit
    (whole_predict : Weights →L[ℝ] Outputs)
    (start_weights : Weights)
    (query_features : Weights)
    (signal : Outputs)
    (noise : Outputs)
    (signal_strength : ℝ)
    (noise_strength : ℝ) :
    let fit :=
      GET_SPLIT_FIT whole_predict start_weights signal noise signal_strength
        noise_strength
    let new_answer   := inner ℝ query_features fit
    let start_answer := inner ℝ query_features start_weights
    let signal_move  :=
      inner ℝ (whole_predict query_features) signal / signal_strength
    let noise_move   :=
      inner ℝ (whole_predict query_features) noise / noise_strength
    new_answer = start_answer + signal_move + noise_move := by
  unfold_named_pieces
  rw [GET_SPLIT_FIT, inner_add_right, adjoint_inner_right, inner_add_right,
    real_inner_smul_right, real_inner_smul_right]
  ring

end Fit

/-! ### With junk features -/

section Junk

variable {RealWeights JunkWeights Weights Outputs : Type*}
  [NormedAddCommGroup RealWeights] [InnerProductSpace ℝ RealWeights]
  [CompleteSpace RealWeights]
  [NormedAddCommGroup JunkWeights] [InnerProductSpace ℝ JunkWeights]
  [CompleteSpace JunkWeights]
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]
  {whole_predict : Weights →L[ℝ] Outputs}
  {real_predict : RealWeights →L[ℝ] Outputs}
  {junk_predict : JunkWeights →L[ℝ] Outputs}

omit [CompleteSpace Weights] [CompleteSpace Outputs] in
/-- The damage the noise does to the answer at a new input. -/
theorem abs_noise_damage_le
    (whole_predict : Weights →L[ℝ] Outputs)
    (query_features : Weights)
    (noise : Outputs)
    {noise_strength junk_strength : ℝ}
    (noise_strength_nonneg : 0 ≤ noise_strength)
    (junk_strength_pos : 0 < junk_strength) :
    let overlap := inner ℝ (whole_predict query_features) noise
    let damage  := |overlap / (noise_strength + junk_strength)|
    let damage_cap :=
      ‖whole_predict query_features‖ * ‖noise‖ / junk_strength  -- Cauchy–Schwarz bounds the overlap
    damage ≤ damage_cap := by
  unfold_named_pieces
  exact abs_div_add_le (abs_real_inner_le_norm _ _) noise_strength_nonneg
    junk_strength_pos

/-- **Benign overfitting.** The whole model `whole_predict` has real features
`real_predict` and junk features `junk_predict` of strength `junk_strength` in
every direction. The signal lies along a direction of strength
`signal_strength` of the real features and the noise along one of strength
`noise_strength`. Then the nearest fit of the whole model fits signal and
noise exactly; it moves the answer at a new input by the two terms below; and
the noise term is at most `‖whole_predict query_features‖ * ‖noise‖ /
junk_strength`, however weak `noise_strength` is. -/
theorem benign_overfitting
    (kernel_is_sum : IS_KERNEL_SUM whole_predict real_predict junk_predict)
    {junk_strength : ℝ}
    (junk_strength_pos : 0 < junk_strength)
    (junk_is_tight : HAS_TIGHT_FEATURES junk_predict junk_strength)
    {signal noise : Outputs}
    {signal_strength noise_strength : ℝ}
    (signal_strength_pos : 0 < signal_strength)
    (noise_strength_nonneg : 0 ≤ noise_strength)
    (signal_is_eigen :
      real_predict (adjoint real_predict signal) = signal_strength • signal)
    (noise_is_eigen :
      real_predict (adjoint real_predict noise) = noise_strength • noise)
    (labels : Outputs)
    (start_weights : Weights)
    (residual_splits :
      GET_RESIDUAL (whole_predict : Weights →ₗ[ℝ] Outputs) labels
        start_weights = signal + noise)
    (query_features : Weights) :
    let signal_total := signal_strength + junk_strength  -- real and junk strengths add (IS_KERNEL_SUM)
    let noise_total  := noise_strength + junk_strength
    let fit :=
      GET_SPLIT_FIT whole_predict start_weights signal noise signal_total
        noise_total
    let fits_exactly := whole_predict fit = labels
    let answer_moves :=
      inner ℝ query_features fit
        = inner ℝ query_features start_weights
          + inner ℝ (whole_predict query_features) signal / signal_total
          + inner ℝ (whole_predict query_features) noise / noise_total
    let noise_term_is_capped :=
      |inner ℝ (whole_predict query_features) noise / noise_total|
        ≤ ‖whole_predict query_features‖ * ‖noise‖ / junk_strength
    fits_exactly ∧ answer_moves ∧ noise_term_is_capped := by
  unfold_named_pieces
  exact ⟨splitFit_fits whole_predict labels start_weights
      (ne_of_gt (by linarith)) (ne_of_gt (by linarith))
      (kernel_eigen_add kernel_is_sum signal_is_eigen
        (junk_is_tight signal))
      (kernel_eigen_add kernel_is_sum noise_is_eigen (junk_is_tight noise))
      residual_splits,
    inner_splitFit whole_predict start_weights query_features signal noise _ _,
    abs_noise_damage_le whole_predict query_features noise
      noise_strength_nonneg junk_strength_pos⟩

end Junk

end SquigglyLine
