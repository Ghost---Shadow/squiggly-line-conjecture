/-
AdamW: weight decay inside Adam's rescaling, and outside it.

Adam divides each gradient by its own size. Put the pull of weight decay into
the gradient first and it is divided too: every weight then moves by the same
amount, whatever its size and whatever the strength of the decay. Apply the
decay after the rescaling (AdamW) and every weight shrinks at the same rate,
`1 - learning_rate * decay` a step, as with plain weight decay.

As in `StepRules.lean`, this is one coordinate of Adam with no memory of
earlier steps.

Definitions: `TAKE_ADAM_STEP_WITH_L2`, `TAKE_ADAMW_STEP`.

Theorems:

* `abs_adamL2Step_sub`            inside Adam, the weight moves by exactly
                                  `learning_rate`, whatever the decay;
* `adamL2Step_of_no_gradient`     with no loss gradient, every weight loses the
                                  same amount;
* `adamL2Step_mul`                a larger loss is a weaker decay;
* `adamWStep_eq`                  AdamW shrinks, then steps;
* `adamWStep_of_no_gradient`      with no loss gradient, AdamW shrinks every
                                  weight at the same rate;
* `iterate_adamWStep_of_no_gradient`  and after `step_count` steps by that
                                  factor to the power `step_count`;
* `adamWStep_mul`                 AdamW does not care how large the loss is.
-/
import SquigglyLine.Supporting.Training.StepRules

namespace SquigglyLine

/-- Adam with the decay inside the loss: the pull `decay * weight` toward zero
is added to the gradient before Adam rescales it.
Python: `weight - learning_rate * TAKE_ADAM_STEP(gradient + decay * weight)`. -/
noncomputable def TAKE_ADAM_STEP_WITH_L2
    (learning_rate decay gradient weight : ℝ) : ℝ :=
  weight - learning_rate * TAKE_ADAM_STEP (gradient + decay * weight)

/-- AdamW: Adam's step on the gradient alone, then the decay, not rescaled.
Python: `weight - learning_rate * TAKE_ADAM_STEP(gradient)
- learning_rate * decay * weight`. -/
noncomputable def TAKE_ADAMW_STEP
    (learning_rate decay gradient weight : ℝ) : ℝ :=
  weight - learning_rate * TAKE_ADAM_STEP gradient
    - learning_rate * decay * weight

/-- **Inside Adam, the strength of the decay is rescaled away.** The weight
moves by exactly `learning_rate`, whatever `decay` is. -/
theorem abs_adamL2Step_sub
    {learning_rate : ℝ}
    {decay : ℝ}
    {gradient : ℝ}
    {weight : ℝ}
    (learning_rate_nonneg : 0 ≤ learning_rate)
    (pull_ne_zero : gradient + decay * weight ≠ 0) :
    let step_size :=
      |TAKE_ADAM_STEP_WITH_L2 learning_rate decay gradient weight - weight|
    step_size = learning_rate := by
  unfold_named_pieces
  -- Adam's step is plus or minus one, so the weight moves by `learning_rate`.
  have adam_step_size :
      |TAKE_ADAM_STEP (gradient + decay * weight)| = 1 :=
    abs_adamStep pull_ne_zero
  rw [TAKE_ADAM_STEP_WITH_L2, sub_sub_cancel_left, abs_neg, abs_mul,
    adam_step_size, mul_one, abs_of_nonneg learning_rate_nonneg]

/-- With no gradient from the loss, decay inside Adam moves every weight toward
zero by the same amount: a large weight and a small one both lose
`learning_rate`. -/
theorem adamL2Step_of_no_gradient
    {decay : ℝ}
    (decay_pos : 0 < decay)
    (learning_rate weight : ℝ) :
    let l2_step   := TAKE_ADAM_STEP_WITH_L2 learning_rate decay 0 weight
    let adam_step := weight - learning_rate * TAKE_ADAM_STEP weight
    l2_step = adam_step := by
  unfold_named_pieces
  have decay_step_is_sign :
      TAKE_ADAM_STEP (decay * weight) = TAKE_ADAM_STEP weight :=
    adamStep_mul decay_pos weight
  rw [TAKE_ADAM_STEP_WITH_L2, zero_add, decay_step_is_sign]

/-- Inside Adam, making the loss `scale` times larger is the same as making
the decay `scale` times weaker. The decay has no strength of its own. -/
theorem adamL2Step_mul
    {scale : ℝ}
    (scale_pos : 0 < scale)
    (learning_rate decay gradient weight : ℝ) :
    let scaled_loss_step :=
      TAKE_ADAM_STEP_WITH_L2 learning_rate decay (scale * gradient) weight
    let weaker_decay_step :=
      TAKE_ADAM_STEP_WITH_L2 learning_rate (decay / scale) gradient weight
    scaled_loss_step = weaker_decay_step := by
  unfold_named_pieces
  have scale_drops_out :
      TAKE_ADAM_STEP (scale * (gradient + decay / scale * weight))
        = TAKE_ADAM_STEP (gradient + decay / scale * weight) :=
    adamStep_mul scale_pos _
  have pull_scaled :
      scale * (gradient + decay / scale * weight)
        = scale * gradient + decay * weight := by
    field_simp
  rw [TAKE_ADAM_STEP_WITH_L2, TAKE_ADAM_STEP_WITH_L2, ← scale_drops_out,
    pull_scaled]

/-- **AdamW shrinks, then steps.** The decay is the factor
`1 - learning_rate * decay` on the weight, exactly as in plain weight decay. -/
theorem adamWStep_eq
    (learning_rate decay gradient weight : ℝ) :
    let adamw_step   := TAKE_ADAMW_STEP learning_rate decay gradient weight
    let shrink_factor := 1 - learning_rate * decay  -- the decay is applied to the weight alone
    let shrunk_then_stepped :=
      shrink_factor * weight - learning_rate * TAKE_ADAM_STEP gradient
    adamw_step = shrunk_then_stepped := by
  unfold_named_pieces
  rw [TAKE_ADAMW_STEP]
  ring

/-- With no gradient from the loss, AdamW shrinks every weight at the same
rate. -/
theorem adamWStep_of_no_gradient
    (learning_rate decay weight : ℝ) :
    let adamw_step    := TAKE_ADAMW_STEP learning_rate decay 0 weight
    let shrink_factor := 1 - learning_rate * decay
    let shrunk_weight := shrink_factor * weight
    adamw_step = shrunk_weight := by
  unfold_named_pieces
  have adam_step_of_zero : TAKE_ADAM_STEP 0 = 0 := by
    simp [TAKE_ADAM_STEP]
  have shrink_then_step :
      TAKE_ADAMW_STEP learning_rate decay 0 weight
        = (1 - learning_rate * decay) * weight
          - learning_rate * TAKE_ADAM_STEP 0 :=
    adamWStep_eq learning_rate decay 0 weight
  rw [shrink_then_step, adam_step_of_zero]
  ring

/-- After `step_count` such steps a weight is
`(1 - learning_rate * decay) ^ step_count` of what it was. -/
theorem iterate_adamWStep_of_no_gradient
    (learning_rate decay weight : ℝ)
    (step_count : ℕ) :
    let trained_weight :=
      (TAKE_ADAMW_STEP learning_rate decay 0)^[step_count] weight
    let shrink_factor  := 1 - learning_rate * decay
    let total_shrink   := shrink_factor ^ step_count  -- one factor per step
    trained_weight = total_shrink * weight := by
  unfold_named_pieces
  induction step_count with
  | zero => simp
  | succ step_count ih =>
    have one_step (current_weight : ℝ) :
        TAKE_ADAMW_STEP learning_rate decay 0 current_weight
          = (1 - learning_rate * decay) * current_weight :=
      adamWStep_of_no_gradient learning_rate decay current_weight
    rw [Function.iterate_succ_apply', ih, one_step]
    ring

/-- AdamW does not care how large the loss is: its decay keeps its strength. -/
theorem adamWStep_mul
    {scale : ℝ}
    (scale_pos : 0 < scale)
    (learning_rate decay gradient weight : ℝ) :
    let scaled_loss_step :=
      TAKE_ADAMW_STEP learning_rate decay (scale * gradient) weight
    let step := TAKE_ADAMW_STEP learning_rate decay gradient weight
    scaled_loss_step = step := by
  unfold_named_pieces
  have scale_drops_out :
      TAKE_ADAM_STEP (scale * gradient) = TAKE_ADAM_STEP gradient :=
    adamStep_mul scale_pos gradient
  rw [TAKE_ADAMW_STEP, TAKE_ADAMW_STEP, scale_drops_out]

end SquigglyLine
