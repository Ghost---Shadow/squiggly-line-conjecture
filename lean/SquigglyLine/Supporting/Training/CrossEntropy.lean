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
* `le_totalLogLoss_sub_along` : and a share `fraction` of the way removes at
  least the share `fraction` of the gap in loss.

Definitions: `APPLY_SOFTMAX`, `GET_CROSS_ENTROPY`, `GET_LOG_LOSS`,
`TAKE_ERROR_STEP`, `GET_TOTAL_LOG_LOSS`.
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import SquigglyLine.Supporting.Training.LeastAction

namespace SquigglyLine

open Real

/-- One score for each example: the outputs of a model on a list of
examples. -/
abbrev ExampleScores (Examples : Type*) := EuclideanSpace ℝ Examples

/-! ### Many classes: softmax -/

section Softmax

variable {Classes : Type*} [Fintype Classes]

/-- The share of class `chosen_class` when the scores are `scores`. -/
noncomputable def APPLY_SOFTMAX
    (scores : Classes → ℝ)
    (chosen_class : Classes) : ℝ :=
  exp (scores chosen_class) / ∑ j, exp (scores j)

/-- The cross-entropy loss of the scores `scores` against the labels
`labels`, written in the scores. -/
noncomputable def GET_CROSS_ENTROPY
    (labels scores : Classes → ℝ) : ℝ :=
  log (∑ j, exp (scores j)) - ∑ i, labels i * scores i

/-- The sum of the exponentials of the scores is positive. -/
theorem sum_exp_pos [Nonempty Classes]
    (scores : Classes → ℝ) :
    let total_weight := ∑ j, exp (scores j)
    0 < total_weight := by
  unfold_named_pieces
  exact Finset.sum_pos (fun j _ => exp_pos (scores j)) Finset.univ_nonempty

/-- Every share is positive. -/
theorem softmax_pos [Nonempty Classes]
    (scores : Classes → ℝ)
    (chosen_class : Classes) :
    let share := APPLY_SOFTMAX scores chosen_class
    0 < share := by
  unfold_named_pieces
  have total_weight_pos : 0 < ∑ j, exp (scores j) := sum_exp_pos scores
  exact div_pos (exp_pos (scores chosen_class)) total_weight_pos

/-- The shares add up to one. -/
theorem sum_softmax [Nonempty Classes]
    (scores : Classes → ℝ) :
    let total_share := ∑ i, APPLY_SOFTMAX scores i
    total_share = 1 := by
  unfold_named_pieces
  have total_weight_pos : 0 < ∑ j, exp (scores j) := sum_exp_pos scores
  simp only [APPLY_SOFTMAX, ← Finset.sum_div]
  exact div_self total_weight_pos.ne'

/-- The usual form of the loss: minus the label-weighted log of the shares. -/
theorem crossEntropy_eq_neg_sum_log [Nonempty Classes]
    {labels : Classes → ℝ}
    (labels_sum_to_one : ∑ i, labels i = 1)
    (scores : Classes → ℝ) :
    let loss      := GET_CROSS_ENTROPY labels scores
    let usual_form := -∑ i, labels i * log (APPLY_SOFTMAX scores i)
    loss = usual_form := by
  unfold_named_pieces
  have total_weight_pos : 0 < ∑ j, exp (scores j) := sum_exp_pos scores
  have log_share (i : Classes) :
      log (APPLY_SOFTMAX scores i) = scores i - log (∑ j, exp (scores j)) := by
    rw [APPLY_SOFTMAX, log_div (exp_pos _).ne' total_weight_pos.ne', log_exp]
  simp only [log_share, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    labels_sum_to_one, GET_CROSS_ENTROPY]
  ring

/-- With at least two classes, every share is below one. -/
theorem softmax_lt_one [Nontrivial Classes]
    (scores : Classes → ℝ)
    (chosen_class : Classes) :
    let share := APPLY_SOFTMAX scores chosen_class
    share < 1 := by
  unfold_named_pieces
  classical
  have total_weight_pos : 0 < ∑ j, exp (scores j) := sum_exp_pos scores
  obtain ⟨other_class, other_ne⟩ := exists_ne chosen_class
  have rest_pos : 0 < ∑ k ∈ Finset.univ.erase chosen_class, exp (scores k) :=
    Finset.sum_pos (fun k _ => exp_pos (scores k))
      ⟨other_class, Finset.mem_erase.mpr ⟨other_ne, Finset.mem_univ _⟩⟩
  -- The total is the chosen weight plus a positive rest.
  have split_total := Finset.add_sum_erase Finset.univ
    (fun k => exp (scores k)) (Finset.mem_univ chosen_class)
  rw [APPLY_SOFTMAX, div_lt_one total_weight_pos]
  linarith

/-- **The loss of a sure label is never zero.** Against the label "class
`chosen_class`, for certain", no finite scores bring the cross-entropy to
zero. -/
theorem crossEntropy_single_pos [Nontrivial Classes] [DecidableEq Classes]
    (scores : Classes → ℝ)
    (chosen_class : Classes) :
    let sure_label : Classes → ℝ := Pi.single chosen_class 1
    let loss := GET_CROSS_ENTROPY sure_label scores
    0 < loss := by
  unfold_named_pieces
  have loss_eq : GET_CROSS_ENTROPY (Pi.single chosen_class 1) scores
      = -log (APPLY_SOFTMAX scores chosen_class) := by
    rw [crossEntropy_eq_neg_sum_log (by simp)]
    simp [Pi.single_apply]
  have share_pos : 0 < APPLY_SOFTMAX scores chosen_class :=
    softmax_pos scores chosen_class
  have share_lt_one : APPLY_SOFTMAX scores chosen_class < 1 :=
    softmax_lt_one scores chosen_class
  rw [loss_eq, neg_pos]
  exact log_neg share_pos share_lt_one

/-- **Prediction minus label.** Move the scores in the direction `direction`.
The loss changes at the rate "share minus label", summed against
`direction`. -/
theorem hasDerivAt_crossEntropy [Nonempty Classes]
    (labels scores direction : Classes → ℝ) :
    let rate := ∑ i, (APPLY_SOFTMAX scores i - labels i) * direction i
    HasDerivAt
      (fun fraction : ℝ =>
        GET_CROSS_ENTROPY labels fun i => scores i + fraction * direction i)
      rate 0 := by
  unfold_named_pieces
  have total_weight_pos : 0 < ∑ j, exp (scores j) := sum_exp_pos scores
  have score_deriv (i : Classes) :
      HasDerivAt (fun fraction : ℝ => scores i + fraction * direction i)
        (direction i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (direction i)).const_add
      (scores i)
  have exp_sum_deriv :
      HasDerivAt
        (fun fraction : ℝ => ∑ j, exp (scores j + fraction * direction j))
        (∑ j, exp (scores j) * direction j) 0 :=
    HasDerivAt.fun_sum fun j _ => by simpa using (score_deriv j).exp
  have exp_sum_ne_zero : (∑ j, exp (scores j + (0 : ℝ) * direction j)) ≠ 0 := by
    simpa using total_weight_pos.ne'
  have label_sum_deriv :
      HasDerivAt
        (fun fraction : ℝ =>
          ∑ i, labels i * (scores i + fraction * direction i))
        (∑ i, labels i * direction i) 0 :=
    HasDerivAt.fun_sum fun i _ => (score_deriv i).const_mul (labels i)
  refine ((exp_sum_deriv.log exp_sum_ne_zero).sub
    label_sum_deriv).congr_deriv ?_
  simp only [zero_mul, add_zero, APPLY_SOFTMAX, Finset.sum_div,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

end Softmax

/-! ### Two classes: the sigmoid -/

section TwoClasses

/-- The cross-entropy loss of one score `score` against a label `label`
between zero and one. -/
noncomputable def GET_LOG_LOSS
    (label score : ℝ) : ℝ :=
  log (1 + exp score) - label * score

/-- The log of the sigmoid, written with the exponential of the score. -/
theorem log_sigmoid
    (score : ℝ) :
    let log_prediction := log (sigmoid score)
    let log_form       := score - log (1 + exp score)
    log_prediction = log_form := by
  unfold_named_pieces
  have ratio_eq : 1 + (exp score)⁻¹ = (1 + exp score) / exp score := by
    have exp_ne_zero := (exp_pos score).ne'
    field_simp
    ring
  rw [sigmoid_def, log_inv, exp_neg, ratio_eq,
    log_div (by positivity) (exp_pos score).ne', log_exp]
  ring

/-- The log of one minus the sigmoid. -/
theorem log_one_sub_sigmoid
    (score : ℝ) :
    let log_complement := log (1 - sigmoid score)
    let log_form       := -log (1 + exp score)
    log_complement = log_form := by
  unfold_named_pieces
  rw [← sigmoid_neg, sigmoid_def, neg_neg, log_inv]

/-- The usual form of the loss, with the sigmoid of the score as the
prediction. -/
theorem logLoss_eq
    (label : ℝ)
    (score : ℝ) :
    let loss := GET_LOG_LOSS label score
    let usual_form :=
      -(label * log (sigmoid score)) - (1 - label) * log (1 - sigmoid score)
    loss = usual_form := by
  unfold_named_pieces
  have log_prediction : log (sigmoid score) = score - log (1 + exp score) :=
    log_sigmoid score
  have log_complement : log (1 - sigmoid score) = -log (1 + exp score) :=
    log_one_sub_sigmoid score
  rw [log_prediction, log_complement, GET_LOG_LOSS]
  ring

/-- **Prediction minus label.** The loss changes with the score at the rate
"sigmoid of the score, minus the label". -/
theorem hasDerivAt_logLoss
    (label : ℝ)
    (score : ℝ) :
    let loss := GET_LOG_LOSS label
    let rate := sigmoid score - label
    HasDerivAt loss rate score := by
  unfold_named_pieces
  have one_add_exp_pos : (0 : ℝ) < 1 + exp score := by positivity
  have log_part :
      HasDerivAt (fun input => log (1 + exp input))
        (exp score / (1 + exp score)) score :=
    ((hasDerivAt_exp score).const_add 1).log one_add_exp_pos.ne'
  have linear_part : HasDerivAt (fun input => label * input) label score := by
    simpa using (hasDerivAt_id score).const_mul label
  refine (log_part.sub linear_part).congr_deriv ?_
  rw [sigmoid_def, exp_neg]
  field_simp
  ring

/-- The slope of the loss, as a function of the score. -/
theorem deriv_logLoss
    (label : ℝ) :
    let loss_slope     := deriv (GET_LOG_LOSS label)
    let expected_slope := fun score => sigmoid score - label
    loss_slope = expected_slope := by
  unfold_named_pieces
  exact funext fun score => (hasDerivAt_logLoss label score).deriv

/-- The loss is convex in the score. -/
theorem convexOn_logLoss
    (label : ℝ) :
    let loss := GET_LOG_LOSS label
    ConvexOn ℝ Set.univ loss := by
  unfold_named_pieces
  have rate_at (score : ℝ) :
      HasDerivAt (GET_LOG_LOSS label) (sigmoid score - label) score :=
    hasDerivAt_logLoss label score
  have slope_eq :
      deriv (GET_LOG_LOSS label) = fun score => sigmoid score - label :=
    deriv_logLoss label
  refine Monotone.convexOn_univ_of_deriv
    (fun score => (rate_at score).differentiableAt) ?_
  rw [slope_eq]
  -- The sigmoid only goes up, so the slope only goes up.
  exact fun _ _ below => sub_le_sub_right (sigmoid_le below) label

/-- For the label "yes" the loss is never zero. -/
theorem logLoss_one_pos
    (score : ℝ) :
    let loss := GET_LOG_LOSS 1 score
    0 < loss := by
  unfold_named_pieces
  have loss_eq : GET_LOG_LOSS 1 score = -log (sigmoid score) := by
    rw [GET_LOG_LOSS, (log_sigmoid score)]
    ring
  rw [loss_eq, neg_pos]
  exact log_neg (sigmoid_pos score) (sigmoid_lt_one score)

/-- **No finite score is best.** For the label "yes", a larger score always
has a smaller loss. -/
theorem strictAnti_logLoss_one :
    let loss_for_yes := GET_LOG_LOSS 1
    StrictAnti loss_for_yes := by
  unfold_named_pieces
  have slope_eq : deriv (GET_LOG_LOSS 1) = fun score => sigmoid score - 1 :=
    deriv_logLoss 1
  refine strictAnti_of_deriv_neg fun score => ?_
  rw [slope_eq]
  exact sub_neg.mpr (sigmoid_lt_one score)

/-- A score whose prediction equals the label is a best score. -/
theorem logLoss_le_of_sigmoid_eq
    {label best_score : ℝ}
    (prediction_matches : sigmoid best_score = label)
    (score : ℝ) :
    let best_loss := GET_LOG_LOSS label best_score
    let loss      := GET_LOG_LOSS label score
    best_loss ≤ loss := by
  unfold_named_pieces
  have rate_at (input : ℝ) :
      HasDerivAt (GET_LOG_LOSS label) (sigmoid input - label) input :=
    hasDerivAt_logLoss label input
  have loss_differentiable : Differentiable ℝ (GET_LOG_LOSS label) :=
    fun input => (rate_at input).differentiableAt
  have slope_eq (input : ℝ) :
      deriv (GET_LOG_LOSS label) input
        = sigmoid input - sigmoid best_score := by
    rw [(rate_at input).deriv, prediction_matches]
  -- Left of the best score the loss falls, right of it the loss rises.
  rcases le_total score best_score with left_of_best | right_of_best
  · have falling : AntitoneOn (GET_LOG_LOSS label) (Set.Iic best_score) :=
      antitoneOn_of_deriv_nonpos (convex_Iic best_score)
        loss_differentiable.continuous.continuousOn
        loss_differentiable.differentiableOn fun input input_inside => by
          rw [interior_Iic] at input_inside
          rw [slope_eq]
          exact sub_nonpos.mpr (sigmoid_le (Set.mem_Iio.mp input_inside).le)
    exact falling left_of_best (Set.mem_Iic.mpr le_rfl) left_of_best
  · have rising : MonotoneOn (GET_LOG_LOSS label) (Set.Ici best_score) :=
      monotoneOn_of_deriv_nonneg (convex_Ici best_score)
        loss_differentiable.continuous.continuousOn
        loss_differentiable.differentiableOn fun input input_inside => by
          rw [interior_Ici] at input_inside
          rw [slope_eq]
          exact sub_nonneg.mpr (sigmoid_le (Set.mem_Ioi.mp input_inside).le)
    exact rising (Set.mem_Ici.mpr le_rfl) right_of_best right_of_best

/-- **A soft label has a finite best score.** For a label strictly between
zero and one, some finite score has the least loss. Compare
`strictAnti_logLoss_one`. -/
theorem exists_best_score
    {label : ℝ}
    (label_pos : 0 < label)
    (label_lt_one : label < 1) :
    ∃ best_score : ℝ, ∀ score : ℝ,
      let best_loss := GET_LOG_LOSS label best_score
      let loss      := GET_LOG_LOSS label score
      best_loss ≤ loss := by
  unfold_named_pieces
  have label_in_range : label ∈ Set.range sigmoid := by
    rw [range_sigmoid]
    exact ⟨label_pos, label_lt_one⟩
  obtain ⟨best_score, best_score_matches⟩ := label_in_range
  exact ⟨best_score, logLoss_le_of_sigmoid_eq best_score_matches⟩

end TwoClasses

/-! ### A linear model, under any reading of the error -/

section AnyError

open ContinuousLinearMap

variable {Weights OtherWeights Outputs : Type*}
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]
  [NormedAddCommGroup OtherWeights] [InnerProductSpace ℝ OtherWeights]
  [CompleteSpace OtherWeights]
  [NormedAddCommGroup Outputs] [InnerProductSpace ℝ Outputs]
  [CompleteSpace Outputs]

/-- One training step, when the loss pushes the outputs `outputs` by
`error_of outputs`. -/
noncomputable def TAKE_ERROR_STEP
    (predict : Weights →L[ℝ] Outputs)
    (error_of : Outputs → Outputs)
    (learning_rate : ℝ)
    (weights : Weights) : Weights :=
  weights - learning_rate • adjoint predict (error_of (predict weights))

/-- Squared error is the case "output minus label". -/
theorem gradientStep_eq_errorStep
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (weights : Weights) :
    let gradient_step :=
      TAKE_GRADIENT_STEP predict labels learning_rate weights
    let error_step :=
      TAKE_ERROR_STEP predict (fun outputs => outputs - labels) learning_rate
        weights
    gradient_step = error_step := by
  unfold_named_pieces
  -- The residual is the error with its sign flipped.
  have residual_flip :
      GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels weights
        = -(predict weights - labels) := by
    simp [GET_RESIDUAL]
  rw [TAKE_GRADIENT_STEP, TAKE_ERROR_STEP, residual_flip, map_neg, smul_neg,
    ← sub_eq_add_neg]

/-- **The same kernel, whatever the loss.** A step moves the outputs by the
kernel `A A†` applied to the error. -/
theorem map_errorStep
    (predict : Weights →L[ℝ] Outputs)
    (error_of : Outputs → Outputs)
    (learning_rate : ℝ)
    (weights : Weights) :
    let stepped_weights :=
      TAKE_ERROR_STEP predict error_of learning_rate weights
    let outputs_after  := predict stepped_weights
    let outputs_before := predict weights
    let kernel_push    :=
      predict (adjoint predict (error_of outputs_before))  -- `K e`, with `K = A A†`
    outputs_after = outputs_before - learning_rate • kernel_push := by
  unfold_named_pieces
  rw [TAKE_ERROR_STEP, map_sub, map_smul]

/-- **Same kernel, same learner, whatever the loss.** Two models with the same
kernel that start from the same outputs have the same outputs after every
step. -/
theorem map_iterate_errorStep_eq
    {predict : Weights →L[ℝ] Outputs}
    {other_predict : OtherWeights →L[ℝ] Outputs}
    (same_kernel : ∀ vector,
      predict (adjoint predict vector)
        = other_predict (adjoint other_predict vector))
    (error_of : Outputs → Outputs)
    (learning_rate : ℝ)
    {start_weights : Weights}
    {other_start_weights : OtherWeights}
    (same_start_outputs :
      predict start_weights = other_predict other_start_weights)
    (step_count : ℕ) :
    let trained_weights :=
      (TAKE_ERROR_STEP predict error_of learning_rate)^[step_count]
        start_weights
    let other_trained_weights :=
      (TAKE_ERROR_STEP other_predict error_of learning_rate)^[step_count]
        other_start_weights
    let outputs       := predict trained_weights
    let other_outputs := other_predict other_trained_weights
    outputs = other_outputs := by
  unfold_named_pieces
  have predict_step (weights : Weights) :
      predict (TAKE_ERROR_STEP predict error_of learning_rate weights)
        = predict weights - learning_rate
          • predict (adjoint predict (error_of (predict weights))) :=
    map_errorStep predict error_of learning_rate weights
  have other_predict_step (weights : OtherWeights) :
      other_predict (TAKE_ERROR_STEP other_predict error_of learning_rate
          weights)
        = other_predict weights - learning_rate
          • other_predict
              (adjoint other_predict (error_of (other_predict weights))) :=
    map_errorStep other_predict error_of learning_rate weights
  induction step_count with
  | zero => exact same_start_outputs
  | succ previous_count earlier_case =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      predict_step, other_predict_step, earlier_case, same_kernel]

/-- Training never leaves the directions of the features. -/
theorem exists_iterate_errorStep
    (predict : Weights →L[ℝ] Outputs)
    (error_of : Outputs → Outputs)
    (learning_rate : ℝ)
    (start_weights : Weights)
    (step_count : ℕ) :
    ∃ vector : Outputs,
      let trained_weights :=
        (TAKE_ERROR_STEP predict error_of learning_rate)^[step_count]
          start_weights
      let moved_weights := start_weights + adjoint predict vector
      trained_weights = moved_weights := by
  unfold_named_pieces
  induction step_count with
  | zero => exact ⟨0, by simp⟩
  | succ previous_count earlier_case =>
    obtain ⟨vector, vector_gives_weights⟩ := earlier_case
    -- One more step adds a pulled-back error to the move.
    refine ⟨vector - learning_rate • error_of (predict
      ((TAKE_ERROR_STEP predict error_of learning_rate)^[previous_count]
        start_weights)), ?_⟩
    rw [Function.iterate_succ_apply', TAKE_ERROR_STEP, map_sub, map_smul,
      ← add_sub_assoc, ← vector_gives_weights]

/-- **Least travel, whatever the loss.** After any number of steps, no weights
with the same outputs are nearer to the start. -/
theorem iterate_errorStep_is_nearest
    (predict : Weights →L[ℝ] Outputs)
    (error_of : Outputs → Outputs)
    (learning_rate : ℝ)
    (start_weights : Weights)
    (step_count : ℕ)
    {other_weights : Weights}
    (same_outputs :
      predict other_weights
        = predict ((TAKE_ERROR_STEP predict error_of learning_rate)^[step_count]
            start_weights)) :
    let trained_weights :=
      (TAKE_ERROR_STEP predict error_of learning_rate)^[step_count]
        start_weights
    let trained_distance := ‖trained_weights - start_weights‖
    let other_distance   := ‖other_weights - start_weights‖
    trained_distance ≤ other_distance := by
  unfold_named_pieces
  obtain ⟨vector, vector_gives_weights⟩ :=
    exists_iterate_errorStep predict error_of learning_rate start_weights
      step_count
  exact norm_sub_le_of_fit_along_features predict vector_gives_weights rfl
    same_outputs

end AnyError

/-! ### Cross-entropy on a linear model -/

section Logistic

open ContinuousLinearMap

variable {Weights Examples : Type*} [Fintype Examples]
  [NormedAddCommGroup Weights] [InnerProductSpace ℝ Weights]
  [CompleteSpace Weights]

/-- The cross-entropy loss of the model `predict` over all examples. Example
`i` has score `predict weights i` and label `labels i`. -/
noncomputable def GET_TOTAL_LOG_LOSS
    (predict : Weights →L[ℝ] ExampleScores Examples)
    (labels : Examples → ℝ)
    (weights : Weights) : ℝ :=
  ∑ i, GET_LOG_LOSS (labels i) (predict weights i)

variable (predict : Weights →L[ℝ] ExampleScores Examples)
  (labels : Examples → ℝ)

omit [CompleteSpace Weights] in
/-- **The gradient is error times features.** Move the weights in the
direction `direction`. The loss changes at the rate "prediction minus label"
on each example, times how fast `direction` moves that example's score. -/
theorem hasDerivAt_totalLogLoss
    (weights direction : Weights) :
    let rate := ∑ i, (sigmoid (predict weights i) - labels i)
      * predict direction i
    HasDerivAt
      (fun fraction : ℝ =>
        GET_TOTAL_LOG_LOSS predict labels (weights + fraction • direction))
      rate 0 := by
  unfold_named_pieces
  refine HasDerivAt.fun_sum fun i _ => ?_
  have score_deriv :
      HasDerivAt
        (fun fraction : ℝ => predict (weights + fraction • direction) i)
        (predict direction i) 0 := by
    have score_line :
        (fun fraction : ℝ => predict (weights + fraction • direction) i)
          = fun fraction =>
            predict weights i + fraction * predict direction i := by
      funext fraction
      simp
    rw [score_line]
    simpa using
      ((hasDerivAt_id (0 : ℝ)).mul_const (predict direction i)).const_add
        (predict weights i)
  exact (hasDerivAt_logLoss (labels i) (predict weights i)).comp_of_eq 0
    score_deriv (by simp)

/-- That rate is the inner product of `direction` with `A†` applied to the
error, so a gradient step on cross-entropy is an `TAKE_ERROR_STEP` whose error
is prediction minus label. -/
theorem inner_adjoint_eq_sum
    (error : ExampleScores Examples)
    (direction : Weights) :
    let pulled_back := inner ℝ (adjoint predict error) direction
    let summed      := ∑ i, error i * predict direction i
    pulled_back = summed := by
  unfold_named_pieces
  rw [adjoint_inner_left]
  simp [PiLp.inner_apply, mul_comm]

variable (start_weights end_weights : Weights)

omit [CompleteSpace Weights] in
/-- **One valley.** On the straight line between two settings of the weights,
the loss is at most the matching blend of the two end losses. -/
theorem totalLogLoss_along_le
    {fraction : ℝ}
    (fraction_nonneg : 0 ≤ fraction)
    (fraction_le_one : fraction ≤ 1) :
    let loss_along :=
      GET_TOTAL_LOG_LOSS predict labels
        (MOVE_ALONG start_weights end_weights fraction)
    let start_loss := GET_TOTAL_LOG_LOSS predict labels start_weights
    let end_loss   := GET_TOTAL_LOG_LOSS predict labels end_weights
    let blend      := (1 - fraction) * start_loss + fraction * end_loss  -- the straight line between the end losses
    loss_along ≤ blend := by
  unfold_named_pieces
  simp only [GET_TOTAL_LOG_LOSS, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have score_blend :
      predict (MOVE_ALONG start_weights end_weights fraction) i
        = (1 - fraction) • predict start_weights i
          + fraction • predict end_weights i := by
    simp [MOVE_ALONG]
    ring
  rw [score_blend]
  -- Each example's loss is convex in its score.
  have loss_convex : ConvexOn ℝ Set.univ (GET_LOG_LOSS (labels i)) :=
    convexOn_logLoss (labels i)
  exact loss_convex.2 (Set.mem_univ _) (Set.mem_univ _)
    (sub_nonneg.mpr fraction_le_one) fraction_nonneg (by ring)

omit [CompleteSpace Weights] in
/-- **No hill between two settings.** The loss on the line is never above the
worse end. -/
theorem totalLogLoss_along_le_max
    {fraction : ℝ}
    (fraction_nonneg : 0 ≤ fraction)
    (fraction_le_one : fraction ≤ 1) :
    let loss_along :=
      GET_TOTAL_LOG_LOSS predict labels
        (MOVE_ALONG start_weights end_weights fraction)
    let start_loss := GET_TOTAL_LOG_LOSS predict labels start_weights
    let end_loss   := GET_TOTAL_LOG_LOSS predict labels end_weights
    let worse_end  := max start_loss end_loss
    loss_along ≤ worse_end := by
  unfold_named_pieces
  have blend_bound :
      GET_TOTAL_LOG_LOSS predict labels
          (MOVE_ALONG start_weights end_weights fraction)
        ≤ (1 - fraction) * GET_TOTAL_LOG_LOSS predict labels start_weights
          + fraction * GET_TOTAL_LOG_LOSS predict labels end_weights :=
    totalLogLoss_along_le predict labels start_weights end_weights
      fraction_nonneg fraction_le_one
  have start_le_max := le_max_left
    (GET_TOTAL_LOG_LOSS predict labels start_weights)
    (GET_TOTAL_LOG_LOSS predict labels end_weights)
  have end_le_max := le_max_right
    (GET_TOTAL_LOG_LOSS predict labels start_weights)
    (GET_TOTAL_LOG_LOSS predict labels end_weights)
  -- A blend of two numbers is no bigger than the bigger one.
  nlinarith [mul_le_mul_of_nonneg_left start_le_max
      (sub_nonneg.mpr fraction_le_one),
    mul_le_mul_of_nonneg_left end_le_max fraction_nonneg]

omit [CompleteSpace Weights] in
/-- **A budget of movement buys at least its share.** Going the share
`fraction` of the way to better weights removes at least the share `fraction`
of the gap in loss. -/
theorem le_totalLogLoss_sub_along
    {fraction : ℝ}
    (fraction_nonneg : 0 ≤ fraction)
    (fraction_le_one : fraction ≤ 1) :
    let loss_along :=
      GET_TOTAL_LOG_LOSS predict labels
        (MOVE_ALONG start_weights end_weights fraction)
    let start_loss := GET_TOTAL_LOG_LOSS predict labels start_weights
    let end_loss   := GET_TOTAL_LOG_LOSS predict labels end_weights
    let gap        := start_loss - end_loss
    let share_of_gap := fraction * gap
    let loss_removed := start_loss - loss_along
    share_of_gap ≤ loss_removed := by
  unfold_named_pieces
  have blend_bound :
      GET_TOTAL_LOG_LOSS predict labels
          (MOVE_ALONG start_weights end_weights fraction)
        ≤ (1 - fraction) * GET_TOTAL_LOG_LOSS predict labels start_weights
          + fraction * GET_TOTAL_LOG_LOSS predict labels end_weights :=
    totalLogLoss_along_le predict labels start_weights end_weights
      fraction_nonneg fraction_le_one
  linarith

end Logistic

end SquigglyLine
