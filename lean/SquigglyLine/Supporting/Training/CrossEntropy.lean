/-
Cross-entropy: classification in the same picture.

The rest of the project trains on squared error. A classifier trains on
cross-entropy, with a softmax (for two classes, a sigmoid) between its scores
and its predictions.

One example:
* `softmax_pos`, `sum_softmax` : a softmax is a set of positive shares.
* `softmax_lt_one`, `crossEntropy_single_pos` : with two or more classes no
  share reaches one, so the loss of a sure label is never zero.
* `hasDerivAt_crossEntropy`, `hasDerivAt_logLoss` : the push on the scores is
  prediction minus label, as it is for squared error.
* `convexOn_logLoss` : the loss is convex in the score.
* `logLoss_one_pos`, `strictAnti_logLoss_one` : for a yes-or-no label no
  finite score is best. A larger score is always better.
* `logLoss_le_of_sigmoid_eq`, `exists_best_score` : for a soft label, the
  score whose prediction equals the label is best, and it is finite.

A model linear in its weights, under any reading of the error:
* `gradientStep_eq_errorStep` : squared error is the case "output minus label".
* `map_errorStep` : a step moves the outputs through the same kernel.
* `map_iterate_errorStep_eq` : same kernel, same outputs at every step.
* `iterate_errorStep_is_nearest` : the weights reached are the nearest to the
  start among all weights with the same outputs.

Cross-entropy on such a model:
* `hasDerivAt_totalLogLoss`, `inner_adjoint_eq_sum` : its error is prediction
  minus label, so it is one of the steps above.
* `totalLogLoss_along_le` : on a straight line in weight space the loss stays
  below the straight line between the two end losses.
* `totalLogLoss_along_le_max` : so there is no hill between two settings.
* `le_totalLogLoss_sub_along` : and a share `t` of the way removes at least
  the share `t` of the gap in loss.
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import SquigglyLine.Supporting.Training.LeastAction

namespace SquigglyLine

open Real

/-! ### Many classes: softmax -/

section Softmax

variable {ι : Type*} [Fintype ι]

/-- The share of class `i` when the scores are `z`. -/
noncomputable def APPLY_SOFTMAX (z : ι → ℝ) (i : ι) : ℝ :=
  exp (z i) / ∑ j, exp (z j)

/-- The cross-entropy loss of the scores `z` against the labels `y`, written in the scores. -/
noncomputable def GET_CROSS_ENTROPY (y z : ι → ℝ) : ℝ :=
  log (∑ j, exp (z j)) - ∑ i, y i * z i

theorem sum_exp_pos [Nonempty ι] (z : ι → ℝ) : 0 < ∑ j, exp (z j) :=
  Finset.sum_pos (fun j _ => exp_pos (z j)) Finset.univ_nonempty

/-- Every share is positive. -/
theorem softmax_pos [Nonempty ι] (z : ι → ℝ) (i : ι) : 0 < APPLY_SOFTMAX z i :=
  div_pos (exp_pos (z i)) (sum_exp_pos z)

/-- The shares add up to one. -/
theorem sum_softmax [Nonempty ι] (z : ι → ℝ) : ∑ i, APPLY_SOFTMAX z i = 1 := by
  simp only [APPLY_SOFTMAX, ← Finset.sum_div]
  exact div_self (sum_exp_pos z).ne'

/-- The usual form of the loss: minus the label-weighted log of the shares. -/
theorem crossEntropy_eq_neg_sum_log [Nonempty ι] {y : ι → ℝ} (hy : ∑ i, y i = 1) (z : ι → ℝ) :
    GET_CROSS_ENTROPY y z = -∑ i, y i * log (APPLY_SOFTMAX z i) := by
  have hlog (i : ι) : log (APPLY_SOFTMAX z i) = z i - log (∑ j, exp (z j)) := by
    rw [APPLY_SOFTMAX, log_div (exp_pos _).ne' (sum_exp_pos z).ne', log_exp]
  simp only [hlog, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hy, GET_CROSS_ENTROPY]
  ring

/-- With at least two classes, every share is below one. -/
theorem softmax_lt_one [Nontrivial ι] (z : ι → ℝ) (i : ι) : APPLY_SOFTMAX z i < 1 := by
  classical
  obtain ⟨j, hj⟩ := exists_ne i
  have hrest : 0 < ∑ k ∈ Finset.univ.erase i, exp (z k) :=
    Finset.sum_pos (fun k _ => exp_pos (z k)) ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩
  have hsplit := Finset.add_sum_erase Finset.univ (fun k => exp (z k)) (Finset.mem_univ i)
  rw [APPLY_SOFTMAX, div_lt_one (sum_exp_pos z)]
  linarith

/-- **The loss of a sure label is never zero.** Against the label "class `i`, for certain", no
finite scores bring the cross-entropy to zero. -/
theorem crossEntropy_single_pos [Nontrivial ι] [DecidableEq ι] (z : ι → ℝ) (i : ι) :
    0 < GET_CROSS_ENTROPY (Pi.single i 1) z := by
  have hloss : GET_CROSS_ENTROPY (Pi.single i 1) z = -log (APPLY_SOFTMAX z i) := by
    rw [crossEntropy_eq_neg_sum_log (by simp)]
    simp [Pi.single_apply]
  rw [hloss, neg_pos]
  exact log_neg (softmax_pos z i) (softmax_lt_one z i)

/-- **Prediction minus label.** Move the scores in the direction `d`. The loss changes at the
rate "share minus label", summed against `d`. -/
theorem hasDerivAt_crossEntropy [Nonempty ι] (y z d : ι → ℝ) :
    HasDerivAt (fun s : ℝ => GET_CROSS_ENTROPY y fun i => z i + s * d i)
      (∑ i, (APPLY_SOFTMAX z i - y i) * d i) 0 := by
  have hscore (i : ι) : HasDerivAt (fun s : ℝ => z i + s * d i) (d i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (d i)).const_add (z i)
  have hexp : HasDerivAt (fun s : ℝ => ∑ j, exp (z j + s * d j)) (∑ j, exp (z j) * d j) 0 :=
    HasDerivAt.fun_sum fun j _ => by simpa using (hscore j).exp
  have hpos : (∑ j, exp (z j + (0 : ℝ) * d j)) ≠ 0 := by
    simpa using (sum_exp_pos z).ne'
  have hlin : HasDerivAt (fun s : ℝ => ∑ i, y i * (z i + s * d i)) (∑ i, y i * d i) 0 :=
    HasDerivAt.fun_sum fun i _ => (hscore i).const_mul (y i)
  refine ((hexp.log hpos).sub hlin).congr_deriv ?_
  simp only [zero_mul, add_zero, APPLY_SOFTMAX, Finset.sum_div, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end Softmax

/-! ### Two classes: the sigmoid -/

section TwoClasses

/-- The cross-entropy loss of one score `z` against a label `y` between zero and one. -/
noncomputable def GET_LOG_LOSS (y z : ℝ) : ℝ :=
  log (1 + exp z) - y * z

theorem log_sigmoid (z : ℝ) : log (sigmoid z) = z - log (1 + exp z) := by
  have hratio : 1 + (exp z)⁻¹ = (1 + exp z) / exp z := by
    have := (exp_pos z).ne'
    field_simp
    ring
  rw [sigmoid_def, log_inv, exp_neg, hratio, log_div (by positivity) (exp_pos z).ne', log_exp]
  ring

theorem log_one_sub_sigmoid (z : ℝ) : log (1 - sigmoid z) = -log (1 + exp z) := by
  rw [← sigmoid_neg, sigmoid_def, neg_neg, log_inv]

/-- The usual form of the loss, with the sigmoid of the score as the prediction. -/
theorem logLoss_eq (y z : ℝ) :
    GET_LOG_LOSS y z = -(y * log (sigmoid z)) - (1 - y) * log (1 - sigmoid z) := by
  rw [log_sigmoid, log_one_sub_sigmoid, GET_LOG_LOSS]
  ring

/-- **Prediction minus label.** The loss changes with the score at the rate "sigmoid of the
score, minus the label". -/
theorem hasDerivAt_logLoss (y z : ℝ) : HasDerivAt (GET_LOG_LOSS y) (sigmoid z - y) z := by
  have hpos : (0 : ℝ) < 1 + exp z := by positivity
  have hsoft : HasDerivAt (fun z => log (1 + exp z)) (exp z / (1 + exp z)) z :=
    ((hasDerivAt_exp z).const_add 1).log hpos.ne'
  have hlin : HasDerivAt (fun z => y * z) y z := by
    simpa using (hasDerivAt_id z).const_mul y
  refine (hsoft.sub hlin).congr_deriv ?_
  rw [sigmoid_def, exp_neg]
  field_simp
  ring

theorem deriv_logLoss (y : ℝ) : deriv (GET_LOG_LOSS y) = fun z => sigmoid z - y :=
  funext fun z => (hasDerivAt_logLoss y z).deriv

/-- The loss is convex in the score. -/
theorem convexOn_logLoss (y : ℝ) : ConvexOn ℝ Set.univ (GET_LOG_LOSS y) :=
  Monotone.convexOn_univ_of_deriv (fun z => (hasDerivAt_logLoss y z).differentiableAt) <| by
    rw [deriv_logLoss]
    exact fun _ _ h => sub_le_sub_right (sigmoid_le h) y

/-- For the label "yes" the loss is never zero. -/
theorem logLoss_one_pos (z : ℝ) : 0 < GET_LOG_LOSS 1 z := by
  have h : GET_LOG_LOSS 1 z = -log (sigmoid z) := by rw [log_sigmoid, GET_LOG_LOSS]; ring
  rw [h, neg_pos]
  exact log_neg (sigmoid_pos z) (sigmoid_lt_one z)

/-- **No finite score is best.** For the label "yes", a larger score always has a smaller
loss. -/
theorem strictAnti_logLoss_one : StrictAnti (GET_LOG_LOSS 1) :=
  strictAnti_of_deriv_neg fun z => by
    rw [deriv_logLoss]
    exact sub_neg.mpr (sigmoid_lt_one z)

/-- A score whose prediction equals the label is a best score. -/
theorem logLoss_le_of_sigmoid_eq {y z₀ : ℝ} (hmatch : sigmoid z₀ = y) (z : ℝ) :
    GET_LOG_LOSS y z₀ ≤ GET_LOG_LOSS y z := by
  have hdiff : Differentiable ℝ (GET_LOG_LOSS y) := fun x => (hasDerivAt_logLoss y x).differentiableAt
  have hderiv (x : ℝ) : deriv (GET_LOG_LOSS y) x = sigmoid x - sigmoid z₀ := by
    rw [(hasDerivAt_logLoss y x).deriv, hmatch]
  rcases le_total z z₀ with hz | hz
  · have hfalling : AntitoneOn (GET_LOG_LOSS y) (Set.Iic z₀) :=
      antitoneOn_of_deriv_nonpos (convex_Iic z₀) hdiff.continuous.continuousOn
        hdiff.differentiableOn fun x hx => by
          rw [interior_Iic] at hx
          rw [hderiv]
          exact sub_nonpos.mpr (sigmoid_le (Set.mem_Iio.mp hx).le)
    exact hfalling hz (Set.mem_Iic.mpr le_rfl) hz
  · have hrising : MonotoneOn (GET_LOG_LOSS y) (Set.Ici z₀) :=
      monotoneOn_of_deriv_nonneg (convex_Ici z₀) hdiff.continuous.continuousOn
        hdiff.differentiableOn fun x hx => by
          rw [interior_Ici] at hx
          rw [hderiv]
          exact sub_nonneg.mpr (sigmoid_le (Set.mem_Ioi.mp hx).le)
    exact hrising (Set.mem_Ici.mpr le_rfl) hz hz

/-- **A soft label has a finite best score.** For a label strictly between zero and one, some
finite score has the least loss. Compare `strictAnti_logLoss_one`. -/
theorem exists_best_score {y : ℝ} (h0 : 0 < y) (h1 : y < 1) :
    ∃ z₀, ∀ z, GET_LOG_LOSS y z₀ ≤ GET_LOG_LOSS y z := by
  have hrange : y ∈ Set.range sigmoid := by
    rw [range_sigmoid]
    exact ⟨h0, h1⟩
  obtain ⟨z₀, hz₀⟩ := hrange
  exact ⟨z₀, logLoss_le_of_sigmoid_eq hz₀⟩

end TwoClasses

/-! ### A linear model, under any reading of the error -/

section AnyError

open ContinuousLinearMap

variable {Θ Θ' Y : Type*}
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
  [NormedAddCommGroup Θ'] [InnerProductSpace ℝ Θ'] [CompleteSpace Θ']
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- One training step, when the loss pushes the outputs `out` by `err out`. -/
noncomputable def TAKE_ERROR_STEP (A : Θ →L[ℝ] Y) (err : Y → Y) (η : ℝ) (θ : Θ) : Θ :=
  θ - η • adjoint A (err (A θ))

/-- Squared error is the case "output minus label". -/
theorem gradientStep_eq_errorStep (A : Θ →L[ℝ] Y) (y : Y) (η : ℝ) (θ : Θ) :
    TAKE_GRADIENT_STEP A y η θ = TAKE_ERROR_STEP A (fun out => out - y) η θ := by
  have hflip : GET_RESIDUAL (A : Θ →ₗ[ℝ] Y) y θ = -(A θ - y) := by
    simp [GET_RESIDUAL]
  rw [TAKE_GRADIENT_STEP, TAKE_ERROR_STEP, hflip, map_neg, smul_neg, ← sub_eq_add_neg]

/-- **The same kernel, whatever the loss.** A step moves the outputs by the kernel `A A†`
applied to the error. -/
theorem map_errorStep (A : Θ →L[ℝ] Y) (err : Y → Y) (η : ℝ) (θ : Θ) :
    A (TAKE_ERROR_STEP A err η θ) = A θ - η • A (adjoint A (err (A θ))) := by
  rw [TAKE_ERROR_STEP, map_sub, map_smul]

/-- **Same kernel, same learner, whatever the loss.** Two models with the same kernel that
start from the same outputs have the same outputs after every step. -/
theorem map_iterate_errorStep_eq {A : Θ →L[ℝ] Y} {B : Θ' →L[ℝ] Y}
    (hK : ∀ v, A (adjoint A v) = B (adjoint B v)) (err : Y → Y) (η : ℝ) {θ₀ : Θ} {θ₀' : Θ'}
    (hstart : A θ₀ = B θ₀') (t : ℕ) :
    A ((TAKE_ERROR_STEP A err η)^[t] θ₀) = B ((TAKE_ERROR_STEP B err η)^[t] θ₀') := by
  induction t with
  | zero => exact hstart
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_errorStep,
      map_errorStep, ih, hK]

/-- Training never leaves the directions of the features. -/
theorem exists_iterate_errorStep (A : Θ →L[ℝ] Y) (err : Y → Y) (η : ℝ) (θ₀ : Θ) (t : ℕ) :
    ∃ v : Y, (TAKE_ERROR_STEP A err η)^[t] θ₀ = θ₀ + adjoint A v := by
  induction t with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨v, hv⟩ := ih
    refine ⟨v - η • err (A ((TAKE_ERROR_STEP A err η)^[n] θ₀)), ?_⟩
    rw [Function.iterate_succ_apply', TAKE_ERROR_STEP, map_sub, map_smul, ← add_sub_assoc, ← hv]

/-- **Least travel, whatever the loss.** After any number of steps, no weights with the same
outputs are nearer to the start. -/
theorem iterate_errorStep_is_nearest (A : Θ →L[ℝ] Y) (err : Y → Y) (η : ℝ) (θ₀ : Θ) (t : ℕ)
    {θ' : Θ} (hsame : A θ' = A ((TAKE_ERROR_STEP A err η)^[t] θ₀)) :
    ‖(TAKE_ERROR_STEP A err η)^[t] θ₀ - θ₀‖ ≤ ‖θ' - θ₀‖ := by
  obtain ⟨v, hv⟩ := exists_iterate_errorStep A err η θ₀ t
  exact norm_sub_le_of_fit_along_features A hv rfl hsame

end AnyError

/-! ### Cross-entropy on a linear model -/

section Logistic

open ContinuousLinearMap

variable {Θ ι : Type*} [Fintype ι]
  [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]

/-- The cross-entropy loss of the model `A` over all examples. Example `i` has score
`A θ i` and label `y i`. -/
noncomputable def GET_TOTAL_LOG_LOSS (A : Θ →L[ℝ] EuclideanSpace ℝ ι) (y : ι → ℝ) (θ : Θ) : ℝ :=
  ∑ i, GET_LOG_LOSS (y i) (A θ i)

variable (A : Θ →L[ℝ] EuclideanSpace ℝ ι) (y : ι → ℝ)

omit [CompleteSpace Θ] in
/-- **The gradient is error times features.** Move the weights in the direction `δ`. The loss
changes at the rate "prediction minus label" on each example, times how fast `δ` moves that
example's score. -/
theorem hasDerivAt_totalLogLoss (θ δ : Θ) :
    HasDerivAt (fun s : ℝ => GET_TOTAL_LOG_LOSS A y (θ + s • δ))
      (∑ i, (sigmoid (A θ i) - y i) * A δ i) 0 := by
  refine HasDerivAt.fun_sum fun i _ => ?_
  have hscore : HasDerivAt (fun s : ℝ => A (θ + s • δ) i) (A δ i) 0 := by
    have hline : (fun s : ℝ => A (θ + s • δ) i) = fun s => A θ i + s * A δ i := by
      funext s
      simp
    rw [hline]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (A δ i)).const_add (A θ i)
  exact (hasDerivAt_logLoss (y i) (A θ i)).comp_of_eq 0 hscore (by simp)

/-- That rate is the inner product of `δ` with `A†` applied to the error, so a gradient step
on cross-entropy is an `TAKE_ERROR_STEP` whose error is prediction minus label. -/
theorem inner_adjoint_eq_sum (e : EuclideanSpace ℝ ι) (δ : Θ) :
    inner ℝ (adjoint A e) δ = ∑ i, e i * A δ i := by
  rw [adjoint_inner_left]
  simp [PiLp.inner_apply, mul_comm]

variable (θ₀ θ₁ : Θ)

omit [CompleteSpace Θ] in
/-- **One valley.** On the straight line between two settings of the weights, the loss is at
most the matching blend of the two end losses. -/
theorem totalLogLoss_along_le {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    GET_TOTAL_LOG_LOSS A y (MOVE_ALONG θ₀ θ₁ t)
      ≤ (1 - t) * GET_TOTAL_LOG_LOSS A y θ₀ + t * GET_TOTAL_LOG_LOSS A y θ₁ := by
  simp only [GET_TOTAL_LOG_LOSS, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hscore : A (MOVE_ALONG θ₀ θ₁ t) i = (1 - t) • A θ₀ i + t • A θ₁ i := by
    simp [MOVE_ALONG]
    ring
  rw [hscore]
  exact (convexOn_logLoss (y i)).2 (Set.mem_univ _) (Set.mem_univ _) (sub_nonneg.mpr h1) h0
    (by ring)

omit [CompleteSpace Θ] in
/-- **No hill between two settings.** The loss on the line is never above the worse end. -/
theorem totalLogLoss_along_le_max {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    GET_TOTAL_LOG_LOSS A y (MOVE_ALONG θ₀ θ₁ t) ≤ max (GET_TOTAL_LOG_LOSS A y θ₀) (GET_TOTAL_LOG_LOSS A y θ₁) := by
  have hblend := totalLogLoss_along_le A y θ₀ θ₁ h0 h1
  have hleft := le_max_left (GET_TOTAL_LOG_LOSS A y θ₀) (GET_TOTAL_LOG_LOSS A y θ₁)
  have hright := le_max_right (GET_TOTAL_LOG_LOSS A y θ₀) (GET_TOTAL_LOG_LOSS A y θ₁)
  nlinarith [mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr h1),
    mul_le_mul_of_nonneg_left hright h0]

omit [CompleteSpace Θ] in
/-- **A budget of movement buys at least its share.** Going the share `t` of the way to
better weights removes at least the share `t` of the gap in loss. -/
theorem le_totalLogLoss_sub_along {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t * (GET_TOTAL_LOG_LOSS A y θ₀ - GET_TOTAL_LOG_LOSS A y θ₁)
      ≤ GET_TOTAL_LOG_LOSS A y θ₀ - GET_TOTAL_LOG_LOSS A y (MOVE_ALONG θ₀ θ₁ t) := by
  linarith [totalLogLoss_along_le A y θ₀ θ₁ h0 h1]

end Logistic

end SquigglyLine
