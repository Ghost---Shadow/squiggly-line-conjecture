/-
Policy gradient is the cross-entropy push, times the reward.

A softmax policy picks action `taken_action` with the share
`APPLY_SOFTMAX scores taken_action` of its scores `scores`. The log of that
share is minus the cross-entropy of the scores against the label "action
`taken_action` was taken". So its rate of change is "action taken minus
prediction", the push of `CrossEntropy.lean` with the sign turned. The expected
reward then changes at the rate: share of each action, times its reward, times
that push.

Definitions: `MARK_ACTION`.

Theorems:

* `log_softmax_eq_neg_crossEntropy`  the log of a policy's share is minus a
                                     cross-entropy;
* `hasDerivAt_log_policy`            the push on the scores is "action taken
                                     minus prediction";
* `hasDerivAt_expectedReward`        the policy gradient.
-/
import SquigglyLine.Supporting.Training.CrossEntropy

namespace SquigglyLine

open Real

variable {Actions : Type*} [Fintype Actions] [DecidableEq Actions]
  [Nonempty Actions]

/-- The label that says "action `taken_action` was taken": one for
`taken_action` and zero for every other action.
Python: `[1 if action == taken_action else 0 for action in actions]`. -/
def MARK_ACTION
    (taken_action : Actions) : Actions → ℝ :=
  fun action => if action = taken_action then 1 else 0

/-- **The log of a policy's share is minus a cross-entropy.** -/
theorem log_softmax_eq_neg_crossEntropy
    (scores : Actions → ℝ)
    (taken_action : Actions) :
    let log_share  := log (APPLY_SOFTMAX scores taken_action)
    let minus_loss := -GET_CROSS_ENTROPY (MARK_ACTION taken_action) scores
    log_share = minus_loss := by
  unfold_named_pieces
  have label_sums_to_one : ∑ i, MARK_ACTION taken_action i = 1 := by
    simp [MARK_ACTION]
  have usual_form :
      GET_CROSS_ENTROPY (MARK_ACTION taken_action) scores
        = -∑ i, MARK_ACTION taken_action i * log (APPLY_SOFTMAX scores i) :=
    crossEntropy_eq_neg_sum_log label_sums_to_one scores
  rw [usual_form]
  simp [MARK_ACTION]

/-- **The push on the scores is "action taken minus prediction".** -/
theorem hasDerivAt_log_policy
    (scores direction : Actions → ℝ)
    (taken_action : Actions) :
    let log_share_along : ℝ → ℝ := fun fraction =>
      log (APPLY_SOFTMAX (fun i => scores i + fraction * direction i)
        taken_action)
    let rate := ∑ i,
      (MARK_ACTION taken_action i - APPLY_SOFTMAX scores i) * direction i
    HasDerivAt log_share_along rate 0 := by
  unfold_named_pieces
  have loss_deriv :
      HasDerivAt
        (fun fraction : ℝ =>
          GET_CROSS_ENTROPY (MARK_ACTION taken_action)
            fun i => scores i + fraction * direction i)
        (∑ i, (APPLY_SOFTMAX scores i - MARK_ACTION taken_action i)
          * direction i) 0 :=
    hasDerivAt_crossEntropy (MARK_ACTION taken_action) scores direction
  have minus_loss_deriv :
      HasDerivAt
        (fun fraction : ℝ =>
          -GET_CROSS_ENTROPY (MARK_ACTION taken_action)
            fun i => scores i + fraction * direction i)
        (-∑ i, (APPLY_SOFTMAX scores i - MARK_ACTION taken_action i)
          * direction i) 0 :=
    loss_deriv.neg
  have log_share_is_minus_loss :
      (fun fraction : ℝ =>
          log (APPLY_SOFTMAX (fun i => scores i + fraction * direction i)
            taken_action))
        = fun fraction =>
          -GET_CROSS_ENTROPY (MARK_ACTION taken_action)
            fun i => scores i + fraction * direction i := by
    funext fraction
    exact log_softmax_eq_neg_crossEntropy _ taken_action
  -- Turning the sign of the loss turns the sign of its push.
  have rate_is_minus_push :
      ∑ i, (MARK_ACTION taken_action i - APPLY_SOFTMAX scores i)
          * direction i
        = -∑ i, (APPLY_SOFTMAX scores i - MARK_ACTION taken_action i)
          * direction i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [log_share_is_minus_loss, rate_is_minus_push]
  exact minus_loss_deriv

/-- **The policy gradient.** The expected reward changes at the rate: the share
of each action, times its reward, times the push "that action minus
prediction". -/
theorem hasDerivAt_expectedReward
    (scores direction rewards : Actions → ℝ) :
    let expected_reward_along : ℝ → ℝ := fun fraction =>
      ∑ action,
        APPLY_SOFTMAX (fun i => scores i + fraction * direction i) action
          * rewards action
    let rate := ∑ action, APPLY_SOFTMAX scores action
      * (rewards action
        * ∑ i, (MARK_ACTION action i - APPLY_SOFTMAX scores i) * direction i)
    HasDerivAt expected_reward_along rate 0 := by
  unfold_named_pieces
  have term_deriv : ∀ action, HasDerivAt
      (fun fraction : ℝ =>
        APPLY_SOFTMAX (fun i => scores i + fraction * direction i) action
          * rewards action)
      (APPLY_SOFTMAX scores action
        * (rewards action
          * ∑ i, (MARK_ACTION action i - APPLY_SOFTMAX scores i)
            * direction i)) 0 := by
    intro action
    have log_policy_deriv :
        HasDerivAt
          (fun fraction : ℝ =>
            log (APPLY_SOFTMAX (fun i => scores i + fraction * direction i)
              action))
          (∑ i, (MARK_ACTION action i - APPLY_SOFTMAX scores i)
            * direction i) 0 :=
      hasDerivAt_log_policy scores direction action
    -- A share is the exponential of its log, so differentiate through `exp`.
    have exp_log_deriv :
        HasDerivAt
          (fun fraction : ℝ =>
            exp (log (APPLY_SOFTMAX
              (fun i => scores i + fraction * direction i) action)))
          (exp (log (APPLY_SOFTMAX
              (fun i => scores i + (0 : ℝ) * direction i) action))
            * ∑ i, (MARK_ACTION action i - APPLY_SOFTMAX scores i)
              * direction i) 0 :=
      log_policy_deriv.exp
    have exp_log_is_share :
        (fun fraction : ℝ =>
            exp (log (APPLY_SOFTMAX
              (fun i => scores i + fraction * direction i) action)))
          = fun fraction =>
            APPLY_SOFTMAX (fun i => scores i + fraction * direction i)
              action := by
      funext fraction
      exact exp_log (softmax_pos _ action)
    have share_at_zero :
        exp (log (APPLY_SOFTMAX
            (fun i => scores i + (0 : ℝ) * direction i) action))
          = APPLY_SOFTMAX scores action := by
      rw [exp_log (softmax_pos _ action)]
      simp
    rw [exp_log_is_share, share_at_zero] at exp_log_deriv
    have times_reward := exp_log_deriv.mul_const (rewards action)
    convert times_reward using 1
    ring
  exact HasDerivAt.fun_sum fun action _ => term_deriv action

end SquigglyLine
