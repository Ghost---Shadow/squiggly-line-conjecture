/-
Policy gradient is the cross-entropy push, times the reward.

A softmax policy picks action `a` with the share `APPLY_SOFTMAX z a` of its
scores `z`. The log of that share is minus the cross-entropy of the scores
against the label "action `a` was taken". So its rate of change is "action
taken minus prediction", the push of `CrossEntropy.lean` with the sign turned.
The expected reward then changes at the rate: share of each action, times its
reward, times that push.

Written in typical Mathlib style; waiting to be ported to `STYLE.md`.

Definitions: `MARK_ACTION`.

Theorems: `log_softmax_eq_neg_crossEntropy`, `hasDerivAt_log_policy`,
`hasDerivAt_expectedReward`.
-/
import SquigglyLine.Supporting.Training.CrossEntropy

namespace SquigglyLine

open Real

variable {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]

/-- The label that says "action `a` was taken": one for `a` and zero for every other action.
Python: `[1 if i == a else 0 for i in actions]`. -/
def MARK_ACTION (a : α) : α → ℝ :=
  fun i => if i = a then 1 else 0

/-- **The log of a policy's share is minus a cross-entropy.** -/
theorem log_softmax_eq_neg_crossEntropy (z : α → ℝ) (a : α) :
    log (APPLY_SOFTMAX z a) = -GET_CROSS_ENTROPY (MARK_ACTION a) z := by
  have hsum : ∑ i, MARK_ACTION a i = 1 := by simp [MARK_ACTION]
  have h : GET_CROSS_ENTROPY (MARK_ACTION a) z
      = -∑ i, MARK_ACTION a i * log (APPLY_SOFTMAX z i) := crossEntropy_eq_neg_sum_log hsum z
  rw [h]
  simp [MARK_ACTION]

/-- **The push on the scores is "action taken minus prediction".** -/
theorem hasDerivAt_log_policy (z dir : α → ℝ) (a : α) :
    HasDerivAt (fun t : ℝ => log (APPLY_SOFTMAX (fun i => z i + t * dir i) a))
      (∑ i, (MARK_ACTION a i - APPLY_SOFTMAX z i) * dir i) 0 := by
  have h : HasDerivAt
      (fun t : ℝ => GET_CROSS_ENTROPY (MARK_ACTION a) fun i => z i + t * dir i)
      (∑ i, (APPLY_SOFTMAX z i - MARK_ACTION a i) * dir i) 0 :=
    hasDerivAt_crossEntropy (MARK_ACTION a) z dir
  have h2 : HasDerivAt
      (fun t : ℝ => -GET_CROSS_ENTROPY (MARK_ACTION a) fun i => z i + t * dir i)
      (-∑ i, (APPLY_SOFTMAX z i - MARK_ACTION a i) * dir i) 0 := h.neg
  have hfun : (fun t : ℝ => log (APPLY_SOFTMAX (fun i => z i + t * dir i) a))
      = fun t => -GET_CROSS_ENTROPY (MARK_ACTION a) fun i => z i + t * dir i := by
    funext t
    exact log_softmax_eq_neg_crossEntropy _ a
  have hrate : ∑ i, (MARK_ACTION a i - APPLY_SOFTMAX z i) * dir i
      = -∑ i, (APPLY_SOFTMAX z i - MARK_ACTION a i) * dir i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hfun, hrate]
  exact h2

/-- **The policy gradient.** The expected reward changes at the rate: the share of each
action, times its reward, times the push "that action minus prediction". -/
theorem hasDerivAt_expectedReward (z dir R : α → ℝ) :
    HasDerivAt (fun t : ℝ => ∑ a, APPLY_SOFTMAX (fun i => z i + t * dir i) a * R a)
      (∑ a, APPLY_SOFTMAX z a
        * (R a * ∑ i, (MARK_ACTION a i - APPLY_SOFTMAX z i) * dir i)) 0 := by
  have hterm : ∀ a, HasDerivAt
      (fun t : ℝ => APPLY_SOFTMAX (fun i => z i + t * dir i) a * R a)
      (APPLY_SOFTMAX z a * (R a * ∑ i, (MARK_ACTION a i - APPLY_SOFTMAX z i) * dir i)) 0 := by
    intro a
    have hexp : HasDerivAt
        (fun t : ℝ => exp (log (APPLY_SOFTMAX (fun i => z i + t * dir i) a)))
        (exp (log (APPLY_SOFTMAX (fun i => z i + (0 : ℝ) * dir i) a))
          * ∑ i, (MARK_ACTION a i - APPLY_SOFTMAX z i) * dir i) 0 :=
      (hasDerivAt_log_policy z dir a).exp
    have hfun : (fun t : ℝ => exp (log (APPLY_SOFTMAX (fun i => z i + t * dir i) a)))
        = fun t => APPLY_SOFTMAX (fun i => z i + t * dir i) a := by
      funext t
      exact exp_log (softmax_pos _ a)
    have h0 : exp (log (APPLY_SOFTMAX (fun i => z i + (0 : ℝ) * dir i) a))
        = APPLY_SOFTMAX z a := by
      rw [exp_log (softmax_pos _ a)]
      simp
    rw [hfun, h0] at hexp
    have hmul := hexp.mul_const (R a)
    convert hmul using 1
    ring
  exact HasDerivAt.fun_sum fun a _ => hterm a

end SquigglyLine
