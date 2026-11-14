# 18. Strong directions first

**In the repository:**
[`SpectralBias.lean`](../lean/SquigglyLine/Supporting/Training/SpectralBias.lean),
note [`spectral-bias.md`](../docs/supporting/training/spectral-bias.md).
**You need:** chapters 10 and 13.

## The idea

People who train networks see a pattern. Early in training the model has
the broad shape of the data and misses the fine detail. The detail comes
later. This is called **spectral bias**: the model is reported to learn
the smooth, slow-changing part of a function first and the fine wiggles
last (**recalled**: Rahaman et al. 2019).

For a model that is linear in its weights, this is one line of algebra
from chapter 10. Along a pattern of strength `strength`, one gradient
step multiplies the error by `1 − learning_rate × strength`. Strong
patterns shrink fast. Weak ones shrink slowly. A pattern of strength
zero does not shrink at all.

> Each direction of the error has its own clock, of about
> `1 / (learning_rate × strength)` steps. A strong direction is learned
> first, no direction can be hurried, and every direction with some
> strength is learned in the end.

## An example you can do by hand

Take learning rate 0.1 and two directions, as in chapter 10. One has
strength 5, so `rate = learning_rate × strength = 0.5`. The other has
strength 0.05, so its rate is 0.005.

The clocks are `1 / 0.5 = 2` steps and `1 / 0.005 = 200` steps.

After 10 steps the share of error left is:

- strong: `0.5^10`, about 0.001. It is learned.
- weak: `0.995^10`, about 0.951. Almost nothing has happened.

After 200 steps the weak direction has `0.995^200`, about 0.37 left. One
clock has run, and about two thirds of the error has gone.

## The statement

```lean
theorem spectral_bias
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    {learning_rate : ℝ}
    {kernel_strength : ℝ}
    (rate_le_one : learning_rate * kernel_strength ≤ 1)
    (start_weights : Weights)
    {direction : Outputs}
    (direction_is_stretched :
      predict (adjoint predict direction) = kernel_strength • direction)
    (step_count : ℕ) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights
    let start_error   := inner ℝ direction
      (GET_RESIDUAL linear_predict labels start_weights)
    let trained_error := inner ℝ direction
      (GET_RESIDUAL linear_predict labels trained_weights)
    let rate          := learning_rate * kernel_strength
    let lower_bound   := (1 - step_count * rate) * |start_error|
    let upper_bound   := Real.exp (-(step_count * rate)) * |start_error|
    let not_hurried   := lower_bound ≤ |trained_error|
    let runs_out      := |trained_error| ≤ upper_bound
    not_hurried ∧ runs_out := by
```

*Read aloud:* along a direction that the kernel only stretches, the
error left after `step_count` steps is at least `1 − step_count × rate`
of what it was and at most `exp(−step_count × rate)` of it. Here `inner`
measures how much of the error lies along `direction`, and `Real.exp` is
the exponential, the number `e` raised to a power. The condition
`rate_le_one` says the step is not too big for this direction.

The second statement compares two directions.

```lean
theorem strong_directions_first
    {learning_rate : ℝ}
    {weak_strength : ℝ}
    {strong_strength : ℝ}
    (learning_rate_nonneg : 0 ≤ learning_rate)
    (weak_le_strong : weak_strength ≤ strong_strength)
    (strong_rate_le_one : learning_rate * strong_strength ≤ 1)
    (step_count : ℕ) :
    let strong_rate  := learning_rate * strong_strength
    let weak_rate    := learning_rate * weak_strength
    let strong_share := (1 - strong_rate) ^ step_count
    let weak_share   := (1 - weak_rate) ^ step_count
    strong_share ≤ weak_share := by
```

*Read aloud:* at every step, the strong direction has no more error
left than the weak one.

Two more results complete the picture.
`inner_residual_iterate_gradientStep` gives the exact share,
`(1 − learning_rate × kernel_strength) ^ step_count`, and
`inner_residual_iterate_of_kernel_eq_zero` says that a direction of
strength zero keeps its error for ever.

## Why it is true

**One step.** The kernel only stretches `direction`, by `kernel_strength`.
A gradient step removes `learning_rate` times the kernel applied to the
error. Along `direction` that is `learning_rate × kernel_strength` of the
error. So the error is multiplied by `1 − learning_rate × kernel_strength`
(`inner_residual_gradientStep`).

**Many steps.** Repeat. Each step multiplies by the same factor, so
`step_count` steps multiply by its power. The directions do not talk to
each other.

**The two bounds.** The share left is `(1 − rate) ^ step_count`. The lower
bound is Bernoulli's inequality, `one_sub_mul_le_pow_one_sub`: raising a
number just below 1 to a power cannot take away more than the power times
the gap. The upper bound uses the fact that `1 − x` is at most `exp(−x)`,
raised to the same power (`pow_one_sub_le_exp`). The comparison of two
directions is `pow_one_sub_anti`: a larger rate, up to 1, leaves a smaller
share.

## What it explains

**The order of learning.** The directions of chapter 10 are learned in
order of strength. The proof does not say which directions are strong in a
real network. For common networks the strong ones are reported to be the
smooth ones. Here the strengths are given, not derived. **open**

**Early stopping.** Suppose the true pattern lies in strong directions and
the noise lies in weak ones. Stop after 20 steps in the example. The
strong share is `0.5^20`, about one in a million. The weak share is about
0.90, and `spectral_bias` says it cannot be below `1 − 20 × 0.005 = 0.9`.
So the pattern is fitted and the noise has hardly been touched. This is
**argued** from the two bounds. That real data splits this way is **open**.

**Grokking.** A network sometimes fits its training data early and only
much later does well on new data. If the part that generalises lies in a
weak direction, its clock is long. The lower bound says nothing visible
happens for about that long, and the upper bound says it does get learned.
**argued**. Whether this is what happens in a real run is **open**.

## How this meets the squiggly line

This is the kernel of chapter 10, read one direction at a time. In the
Fourier model the strength of a frequency is the square of the size its
coefficient is allowed. If high frequencies get small sizes, the smooth
part is learned first and the squiggles last. So the order in which
squiggles appear in training is set by the same sizes that set how
squiggly the model is at the start.

## What is not shown

- **Deep networks.** The kernel of a deep network changes while it
  trains. The statement here is for a fixed kernel. **open**
- **That smooth means strong.** Here the strengths are given, not
  derived. **open**
- **Step size.** The bounds need `learning_rate × strength ≤ 1` for the
  direction in question. Chapter 19 covers larger steps.

## Check yourself

1. The learning rate is 0.01 and a direction has strength 20. What is its
   clock, and how much error is left after 5 steps?
2. A direction has strength 0. After a million steps, how much of its
   error is left?
3. Directions of strength 2 and 3 are trained with learning rate 0.1.
   Which has less error left after 4 steps?

**Answers.** (1) The rate is `0.01 × 20 = 0.2`, so the clock is 5 steps.
After 5 steps the share is `0.8^5`, about 0.33. It lies between the bounds
`1 − 5 × 0.2 = 0` and `exp(−1)`, about 0.37. (2) All of it, by
`inner_residual_iterate_of_kernel_eq_zero`. (3) The one of strength 3:
`0.7^4` is about 0.24, and `0.8^4` is about 0.41. That is
`strong_directions_first` with rates 0.3 and 0.2.

Previous: [17. The shortest trip](17-the-shortest-trip.md) · Next: [19. The largest step](19-the-largest-step.md)
