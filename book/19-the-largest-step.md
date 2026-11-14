# 19. The largest step

**In the repository:**
[`EdgeOfStability.lean`](../lean/SquigglyLine/Supporting/Training/EdgeOfStability.lean),
[`Optimisers.lean`](../lean/SquigglyLine/Supporting/Training/Optimisers.lean),
notes [`edge-of-stability.md`](../docs/supporting/training/edge-of-stability.md)
and [`spectral-bias.md`](../docs/supporting/training/spectral-bias.md).
**You need:** chapters 10, 13 and 18.

## The idea

Every practitioner has met a learning rate that is too big. The loss
jumps about, then runs off to infinity. There is a largest step that
training can take.

Chapter 18 gave the reason. Along a direction of strength `strength`, a
step multiplies the error by `1 − learning_rate × strength`. That factor
is below one in size, and the error shrinks, exactly when
`learning_rate × strength` is between 0 and 2. At 2 the factor is −1. The
error flips sign and never dies down. Past 2 it grows.

This is the **edge of stability**. People also report that when a
network is trained with plain gradient descent, the sharpness of the loss
climbs until it sits at about `2 / learning_rate` and hovers there
(**recalled**: Cohen et al. 2021). For a model that is linear in its
weights, the number 2 is exact.

> A direction is stable exactly when the learning rate is below
> `2 / strength`. The sharpest direction sets the largest step.

## An example you can do by hand

A direction has strength 10 and the error starts at 8. Try three
learning rates.

| learning rate | `learning_rate × strength` | factor | errors |
|---|---|---|---|
| 0.15 | 1.5 | −0.5 | 8, −4, 2, −1 |
| 0.20 | 2 | −1 | 8, −8, 8, −8 |
| 0.25 | 2.5 | −1.5 | 8, −12, 18, −27 |

The edge is `2 / 10 = 0.2`. Below it the error shrinks, and the sign
flips because the factor is negative. On it the error swings for ever.
Past it, after 3 steps the size is `8 × 1.5³ = 27`. The theorem below
promises at least `8 × (1 + 3 × 0.5) = 20`. It holds.

## The statement

```lean
theorem stable_iff_lt_two_div
    {learning_rate : ℝ}
    {kernel_strength : ℝ}
    (learning_rate_pos : 0 < learning_rate)
    (kernel_strength_pos : 0 < kernel_strength) :
    let factor_is_below_one := |1 - learning_rate * kernel_strength| < 1
    let step_is_below_edge  := learning_rate < 2 / kernel_strength  -- `rate < 2`, divided by `kernel_strength`
    factor_is_below_one ↔ step_is_below_edge := by
```

*Read aloud:* the factor is below one in size exactly when the learning
rate is below `2 / kernel_strength`. The sign `↔` means "exactly when".
The bars `| |` are the size of a number without its sign.

```lean
theorem grows_past_edge
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    {learning_rate : ℝ}
    {kernel_strength : ℝ}
    (rate_past_edge : 2 ≤ learning_rate * kernel_strength)
    (start_weights : Weights)
    {direction : Outputs}
    (direction_is_stretched :
      predict (adjoint predict direction) = kernel_strength • direction)
    (step_count : ℕ) :
```

*Read aloud:* past the edge, the error along `direction` after
`step_count` steps is at least `1 + step_count × (rate − 2)` times what it
was, with `rate = learning_rate × kernel_strength`. That grows without
limit. The quote stops before the `let` lines, which name the start and
trained sizes of the error. The sister results are `shrinks_below_edge`, where the error
never grows, and `holds_at_edge`, where it keeps its size.

## Why it is true

**The factor.** By chapter 18, the error after `step_count` steps is the
factor to the power `step_count`, times the start
(`abs_inner_residual_iterate_gradientStep`). So everything turns on
whether `|1 − rate|` is below, at or above one. That is
`abs_one_sub_lt_one_iff`: the factor is below one in size exactly when
`rate` is between 0 and 2. Divide by `kernel_strength` for
`stable_iff_lt_two_div`.

**Past the edge.** Then `|1 − rate| = rate − 1` is at least 1, and a
power of `1 + (rate − 2)` is at least `1 + step_count × (rate − 2)`. That
is Bernoulli's inequality again (`one_add_mul_le_abs_pow`).

## Four changes to the step

`Optimisers.lean` follows the same factor through four common changes.

**A schedule.** If the learning rate changes from step to step, what is
left of the error is the product of the factors
(`runSchedule_eq`). While every `learning_rate × strength` is between 0
and 2, the error never grows (`abs_runSchedule_le`). A step that is too
large for a direction makes it grow (`one_lt_abs_one_sub`). Warmup starts
small so that the sharpest directions are not hit with a factor above one
before they have settled. That reading of warmup is **argued**.

**The condition number.** Say the strengths lie between `weakest` and
`strongest`.

```lean
theorem abs_one_sub_best_step_le
    {weakest strongest strength : ℝ}
    (weakest_pos : 0 < weakest)
    (weakest_le_strongest : weakest ≤ strongest)
    (weakest_le_strength : weakest ≤ strength)
    (strength_le_strongest : strength ≤ strongest) :
    let best_step := 2 / (weakest + strongest)  -- balances the two ends of the range
    let factor_size := |1 - best_step * strength|
    let speed := (strongest - weakest) / (strongest + weakest)
    factor_size ≤ speed := by
```

*Read aloud:* with the step `2 / (weakest + strongest)`, every direction
shrinks by at least `(strongest − weakest) / (strongest + weakest)` per
step. By `one_sub_best_step_at_weakest` the weakest direction shrinks by
exactly that, so no direction can be promised more. With strengths from 1
to 9 the best step is `2 / 10 = 0.2`. The factors are 0.8 for strength 1
and −0.8 for strength 9, and the bound is `8 / 10 = 0.8`. The more uneven
the strengths, the closer that speed is to 1.

**Momentum.** With momentum `momentum`, the oscillation that never dies
sits at `learning_rate × strength = 2 × (1 + momentum)` instead of 2
(`momentumStep_alternating`, `iterate_momentumStep_alternating`). With no
momentum this is the plain edge (`momentumStep_of_no_momentum`).

**Steps on part of the data.** An average of steps, each on one client's
gradient, is one step on the averaged gradient (`sum_smul_step_eq_step`).
With one example per client and equal shares, a step on a random example
is the full step on average (`mean_step_eq_step`). That is stochastic
gradient descent in the mean, and federated averaging after one local
step.

## What it explains

It explains where the number `2 / learning_rate` comes from, and why the
loss of a model near the edge swings from side to side. It also says why
a bad condition number slows training: the one step has to be small
enough for the strongest direction, and then the weakest crawls.

It does not explain the climb of the sharpness, nor why training
survives at the edge. In a linear model nothing changes the strengths,
and past the edge the model blows up.

## How this meets the squiggly line

The strength is the kernel's (chapter 10), so the edge is a fact about
the kernel and the learning rate together. The note on flat minima shows
that rescaling the weights changes the step size by the square of the
scale, so what matters is the product `learning_rate × strength`, which
rescaling leaves alone. A squigglier model has stronger directions, so
for a fixed learning rate it sits nearer the edge. The averaging result
is the idea of chapter 15.

## What is not shown

- **Why sharpness rises during training.** **open**
- **Why training survives at the edge.** **open**
- **Mini-batches and momentum.** Only plain gradient descent has the edge
  at 2. The momentum edge is proved for its alternating error only. That
  directions below it are stable is not shown. Nor is the noise of a
  random example around its mean, nor federated averaging after more than
  one local step.
- **Real networks.** All of it is for a fixed kernel.

## Check yourself

1. A direction has strength 50. What is the largest stable learning rate?
2. With strength 4 and learning rate 0.4, the error starts at 5. What
   are the next three errors?
3. Strengths run from 2 to 8. What is the best step, and how much does the
   weakest direction shrink per step?

**Answers.** (1) Below `2 / 50 = 0.04`, by `stable_iff_lt_two_div`.
(2) The rate is 1.6 and the factor is −0.6, so the errors are −3, 1.8,
−1.08, by `shrinks_below_edge`. (3) `2 / (2 + 8) = 0.2`. The weakest
factor is `1 − 0.2 × 2 = 0.6`, which is `(8 − 2) / (8 + 2)`, by
`one_sub_best_step_at_weakest`.

Previous: [18. Strong directions first](18-strong-directions-first.md) · Next: [20. Weight decay and early stopping](20-weight-decay-and-early-stopping.md)
