# 20. Weight decay and early stopping

**In the repository:**
[`WeightDecay.lean`](../lean/SquigglyLine/Supporting/Training/WeightDecay.lean),
note [`weight-decay.md`](../docs/supporting/training/weight-decay.md).
**You need:** chapters 10 and 13.

## The idea

People who train models use three habits to keep them from fitting
noise. **Weight decay** pulls the weights back a little at every step.
**Early stopping** ends training before the loss reaches zero. **Spare
parameters** means using a model far bigger than the data needs. They
look unlike each other. The first two are known to act alike
(**recalled**: Goodfellow, Bengio and Courville 2016, section 7.8).

Chapter 10 gives the way to see why. Along a pattern of the labels with
strength `kernel_strength`, training shrinks the error by a fixed factor
per step. Weight decay adds a penalty `decay_strength` on how far the
weights have moved from where they started. Then the error along that
pattern does not go to zero. It comes to rest.

> Weight decay leaves the share `decay_strength / (kernel_strength +
> decay_strength)` of the error. Early stopping after `step_count` steps
> leaves no more than the share weight decay leaves at
> `decay_strength = 1 / (learning_rate × step_count)`.

A pattern stronger than the penalty is learned almost fully. A pattern
weaker than the penalty is hardly touched.

## An example you can do by hand

One weight, one feature of size 2, so the kernel strength is
`2 × 2 = 4`. The label is 10 and the weight starts at 0. The error at the
start is 10.

With `decay_strength = 1`, the fit moves the weight by
`adjoint × error / (strength + decay)`. The adjoint of the feature
applied to the error is `2 × 10 = 20`, so the weight moves by
`20 / (4 + 1) = 4`. The model now says `2 × 4 = 8`. The error left is 2.
That is `1 / (4 + 1) = 0.2` of 10, the share the formula gives.

Check that it is a resting point. The pull of the data is the feature
times the error left: `2 × 2 = 4`. The pull of the penalty is
`decay_strength × (weight − start) = 1 × 4 = 4`. They balance. With
`learning_rate = 0.1` one step of gradient descent with decay gives
`4 + 0.1 × 4 − 0.1 × 1 × 4 = 4`. The weight does not move.

Now stop early instead. Take `learning_rate = 0.1`, strength 5 and
`step_count = 10`, so the rate per step is `0.1 × 5 = 0.5`. After ten
steps the share left is `0.5 ^ 10`, about 0.001. The bound is
`1 / (1 + 10 × 0.5) = 1 / 6`, about 0.17, and that is exactly what weight
decay with `decay_strength = 1 / (0.1 × 10) = 1` leaves:
`1 / (5 + 1) = 1 / 6`.

For a weak pattern, strength 0.05, the rate is 0.005. After ten steps the
share left is `0.995 ^ 10`, about 0.951. The bound is `1 / 1.05`, about
0.952. Both habits leave almost all of it.

## The statement

```lean
/-- **Early stopping cuts at least as hard as weight decay.** After
`step_count` steps at rate `rate` the share of the error left is at most
`1 / (1 + step_count * rate)`. -/
theorem early_stopping_le_ridge
    {rate : ℝ}
    (rate_nonneg : 0 ≤ rate)
    (rate_le_one : rate ≤ 1)
    (step_count : ℕ) :
    let stopped_share := (1 - rate) ^ step_count
    let ridge_share   := 1 / (1 + step_count * rate)
    stopped_share ≤ ridge_share := by
```

*Read aloud:* after `step_count` steps with rate `rate` per step, the
error left is at most one over one plus steps times rate.

Here `rate` is `learning_rate × kernel_strength`, the number from
chapter 10. The name `ridge_share` is the share weight decay leaves
once it is matched to the stopping time. A **ridge** fit is the old
statistics name for the weight-decay fit.

```lean
/-- **The matching penalty.** Weight decay with
`decay_strength = 1 / (learning_rate * step_count)` leaves the share
`1 / (1 + step_count * (learning_rate * kernel_strength))`. -/
theorem ridge_share_eq
    {learning_rate : ℝ}
    {kernel_strength : ℝ}
    {step_count : ℕ}
    (learning_rate_pos : 0 < learning_rate)
    (step_count_pos : 0 < step_count)
    (kernel_strength_nonneg : 0 ≤ kernel_strength) :
    let decay_strength := 1 / (learning_rate * step_count)  -- the penalty that matches `step_count` steps of early stopping
    let ridge_share    := decay_strength / (kernel_strength + decay_strength)
    let stopped_share  :=
      1 / (1 + step_count * (learning_rate * kernel_strength))
    ridge_share = stopped_share := by
```

*Read aloud:* the share weight decay leaves, at the penalty one over
learning rate times steps, is the same number as the bound on early
stopping.

```lean
/-- **What weight decay leaves.** The share
`decay_strength / (kernel_strength + decay_strength)` of the error. -/
theorem residual_ridgeFit
    (strengths_sum_ne_zero : kernel_strength + decay_strength ≠ 0)
    (residual_is_stretched :
      predict (adjoint predict
        (GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
          start_weights))
        = kernel_strength
          • GET_RESIDUAL (predict : Weights →ₗ[ℝ] Outputs) labels
              start_weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let ridge_fit :=
      GET_RIDGE_FIT predict labels start_weights kernel_strength
        decay_strength
    let ridge_residual :=
      GET_RESIDUAL linear_predict labels ridge_fit
    let start_residual :=
      GET_RESIDUAL linear_predict labels start_weights
    let share_left     :=
      decay_strength / (kernel_strength + decay_strength)  -- the penalty's part of the total pull
    let left_over      := share_left • start_residual
    ridge_residual = left_over := by
```

*Read aloud:* if the error at the start is a pattern the kernel
stretches by `kernel_strength`, then the error at the weight-decay fit is
the start error times `decay_strength / (kernel_strength +
decay_strength)`.

`residual_is_stretched` is that condition: the kernel applied to the
error is `kernel_strength` times the error, as in chapter 10. `GET_RIDGE_FIT`
is the start weights plus the adjoint of the error divided by
`kernel_strength + decay_strength`. The theorems `ridge_stationary` and
`decayStep_ridgeFit` say that this fit is where gradient descent with
weight decay (`TAKE_DECAY_STEP`) stays put, which the example checked
for one weight.

## Why it is true

**The share.** The fit moves the weights by the adjoint of the error,
divided by the total `kernel_strength + decay_strength`. The model's
answer moves by the kernel applied to the error, divided by the same
total. The kernel gives `kernel_strength` times the error, so the error
falls by the fraction `kernel_strength / (kernel_strength +
decay_strength)`. What is left is the rest, which is
`decay_strength / (kernel_strength + decay_strength)`. In Lean this is
`residual_after_fit` and then `share_coefficient`.

**Early stopping.** The factor per step is `1 − rate`. The number
`1 − rate` is at most `exp(−rate)`, so `step_count` steps leave at most
`exp(−step_count × rate)`. And `exp(x)` is at least `1 + x`, so that is
at most `1 / (1 + step_count × rate)`. Those are the three lines of the
`calc` chain.

**The match.** Put `decay_strength = 1 / (learning_rate × step_count)`
into the weight-decay share and clear the fractions. It becomes
`1 / (1 + step_count × learning_rate × kernel_strength)`. This is
`field_simp` and `ring`.

## What it explains

People often use weight decay and early stopping as if either would do.
The proof says why. Both put a floor under the strength of every
pattern. A pattern weaker than the floor is not learned. One stronger is
learned almost as before. Training for longer is the same as turning the
penalty down. The note adds that the weight-decay fit moves the answer at
a new input by `overlap / (kernel_strength + decay_strength)`
(`inner_ridgeFit`). That is the same formula as when a pile of spare
features each add strength to every pattern. So a model with many spare
parameters acts like a smaller one with weight decay.

## How this meets the squiggly line

This uses the kernel and the one factor per step of chapters 10 and 13.
It also uses travel (chapter 9). A weak pattern is a long trip in weight
space, and a long trip disturbs the function everywhere. Each habit
refuses the long trips and takes the short ones.

## What is not shown

- The penalty pulls the weights towards where they started. With a start
  at zero that is ordinary weight decay. Otherwise the two differ.
- The statements follow one pattern of the labels. The patterns add
  because the model is linear, but the sum is not written out.
- This is a model linear in its weights with squared error and a fixed
  kernel. Weight decay inside Adam behaves differently. Deep networks
  are **open**.

## Check yourself

1. The decay is 3 and a pattern has strength 1. What share of the error
   is left?
2. `learning_rate = 0.05`, strength 10, stopped after 20 steps. Give the
   bound on the share left, and the matching decay.
3. The overlap with a new input is 6 and the strength is 2. How far does
   the answer move with decay 1? With decay 4?

**Answers.** (1) `3 / (1 + 3) = 0.75`, by `residual_ridgeFit`. (2) The
rate is `0.05 × 10 = 0.5`, so by `early_stopping_le_ridge` the share is at
most `1 / (1 + 20 × 0.5) = 1 / 11`. The matching decay is
`1 / (0.05 × 20) = 1`, and `1 / (10 + 1) = 1 / 11` agrees, as
`ridge_share_eq` says. (3) By `inner_ridgeFit` the shift is
`6 / (2 + 1) = 2` and `6 / (2 + 4) = 1`.

Previous: [19. The largest step](19-the-largest-step.md) · Next: [21. Dropout, noise and other regularisers](21-dropout-and-noise.md)
