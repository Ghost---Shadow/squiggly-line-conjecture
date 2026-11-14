# 23. Adam, AdamW and clipping

**In the repository:**
[`StepRules.lean`](../lean/SquigglyLine/Supporting/Training/StepRules.lean),
[`AdamW.lean`](../lean/SquigglyLine/Supporting/Training/AdamW.lean),
note [`step-rules.md`](../docs/supporting/training/step-rules.md).
**You need:** chapters 9, 10, 18 and 20.

## The idea

Every chapter so far trained with plain gradient descent: the step is in
proportion to the gradient. Most networks are trained with something
else. If you have used Adam, you have seen that it does not much care how
large the loss is. If you have used AdamW, you have seen that its weight
decay is a separate setting that behaves.

This chapter takes the simplest form of Adam, one weight at a time and
with no memory of earlier steps. Adam divides the gradient by its own
size. What is left is its sign.

> With no memory, an Adam step is the sign of the gradient. So a gap
> closes by `learning_rate` per step whatever the strength, and decay
> put inside the rescaling is divided away with everything else.

The same chapter covers **gradient clipping**, which cuts a long gradient
down to a limit, and says what it does to travel.

## An example you can do by hand

A weight is off by a gap of 3, and the learning rate is 0.5.

- Under plain gradient descent (chapter 18) a direction of strength 100
  has factor `1 − 0.5 × 100`, far below minus one, so it blows up. A
  direction of strength 0.01 has factor 0.995, so after 6 steps the gap is
  still about 2.9.
- Under the sign rule the gap goes 3, 2.5, 2, 1.5, 1, 0.5, 0. That is 6
  steps, for any strength.

Now weight decay with `decay = 0.5` and `learning_rate = 0.1`, and no
gradient from the loss.

- Decay inside Adam: a weight of 4 and a weight of 0.1 both lose 0.1 a
  step. The small one is gone in one step. The pull is not in proportion
  to the weight.
- AdamW: every weight is multiplied by `1 − 0.1 × 0.5 = 0.95` a step.
  After 10 steps each is 0.95 to the power 10, about 0.60, of what it was.

Clipping: with `limit = 2` and `learning_rate = 0.1`, a gradient of
length 100 is cut to length 2. After 50 steps the weights have moved at
most `50 × 0.1 × 2 = 10`, whatever the gradients were.

## The statement

```lean
/-- **The step is the sign of the gradient.** -/
theorem adamStep_eq_sign
    (gradient : ℝ) :
    let step          := TAKE_ADAM_STEP gradient
    let gradient_sign : ℝ := SignType.sign gradient  -- minus one, zero or one
    step = gradient_sign := by
```

*Read aloud:* an Adam step with no memory equals minus one, zero or one,
the sign of the gradient.

`TAKE_ADAM_STEP gradient` is the gradient divided by its own size,
`gradient / √(gradient²)`. The theorem `adamStep_mul` says that
multiplying the loss by a positive number changes nothing, and
`abs_adamStep` says every coordinate with a gradient moves the same
distance.

```lean
theorem abs_sub_signStep
    {gap : ℝ}
    {learning_rate : ℝ}
    (learning_rate_nonneg : 0 ≤ learning_rate)
    (learning_rate_le_gap : learning_rate ≤ |gap|) :
    let step : ℝ       := learning_rate * SignType.sign gap
    let remaining_gap  := |gap - step|
    let closed_gap     := |gap| - learning_rate  -- the step is `learning_rate` long, aimed at zero
    remaining_gap = closed_gap := by
```

*Read aloud:* a step of size `learning_rate` against the sign of the
error leaves a gap of `|gap| - learning_rate`, so the strength of the
direction never appears.

```lean
theorem adamWStep_eq
    (learning_rate decay gradient weight : ℝ) :
    let adamw_step   := TAKE_ADAMW_STEP learning_rate decay gradient weight
    let shrink_factor := 1 - learning_rate * decay  -- the decay is applied to the weight alone
    let shrunk_then_stepped :=
      shrink_factor * weight - learning_rate * TAKE_ADAM_STEP gradient
    adamw_step = shrunk_then_stepped := by
```

*Read aloud:* AdamW shrinks the weight by `1 - learning_rate × decay`,
then takes Adam's step.

`TAKE_ADAMW_STEP` takes Adam's step on the loss gradient alone and then
applies the decay. `TAKE_ADAM_STEP_WITH_L2` is the other form: the pull
`decay * weight` is added to the gradient first, and Adam rescales the
sum.

The other results of the two files are named here. For the inside form,
`abs_adamL2Step_sub` says the weight moves by exactly `learning_rate`
whatever `decay` is, `adamL2Step_of_no_gradient` says a large weight and
a small one lose the same amount, and `adamL2Step_mul` says a larger loss
is the same as a weaker decay. For AdamW, `adamWStep_of_no_gradient` and
`iterate_adamWStep_of_no_gradient` give the factor
`(1 - learning_rate × decay)` per step, to the power `step_count` after
that many steps, and `adamWStep_mul` says the size of the loss does not
change the decay. For clipping, `norm_clip_le` says a clipped gradient is
no longer than the limit, `clip_of_norm_le` says a gradient within the
limit is left alone, and `norm_sum_clip_le` says

```
travel  ≤  step_count × (|learning_rate| × limit)
```

## Why it is true

**Adam.** The size of a real number is the square root of its square.
Dividing a number by its size leaves its sign: plus one if it was
positive, minus one if negative, zero if it was zero. That is
`adamStep_eq_sign`, proved by splitting into the three cases. A positive
scale does not change a sign, which gives `adamStep_mul`. A gap that is
at least one step long loses exactly one step, on either side of zero,
which gives `abs_sub_signStep`.

**Inside or outside.** Put the decay inside, and Adam sees one number,
the gradient plus `decay × weight`, and returns its sign. Both the size of
the loss and the size of the decay are gone. Put it outside, and the
shrink is a plain multiplication of the weight, so `adamWStep_eq` is
just the two terms collected. Repeating it `step_count` times gives the
power.

**Clipping.** The clipped gradient is the gradient times
`min 1 (limit / ‖gradient‖)`. That scale is at most `limit / ‖gradient‖`,
so the length is at most `limit`. Each step is then at most
`|learning_rate| × limit`, and the triangle inequality adds them up.

## What it explains

- **Adam trains fast and ignores the scale of the loss.** Chapter 18 said
  strong directions are learned first and weak ones wait, each on its own
  clock. The sign rule has one clock for all of them: a gap of `gap` takes
  `|gap| / learning_rate` steps. That Adam removes the wait for weak
  directions is **argued** from the two proved rates. It is a reason Adam
  can fit noise sooner.
- **Why AdamW replaced Adam with an L2 penalty** (**recalled**: Loshchilov
  and Hutter 2019). Chapter 20 read weight decay as a floor on travel.
  Inside Adam that floor has no fixed height, because the loss can be
  rescaled to move it. Only the outside form keeps it.
- **Why clipping is used where one bad step is costly** (**recalled**:
  Pascanu, Mikolov and Bengio 2013). It is a cap on travel: a fit at
  distance `gap` cannot be reached in fewer than
  `gap / (learning_rate × limit)` steps.

The file also holds two smaller results on the same theme. Confining the
weights to a subspace never shortens the trip, `travel_le_travel_comp`.
Rounding the weights by `weight_change` moves each output by at most
`‖weight_change‖` times the size of the features,
`abs_liftedModel_add_sub_le`, and the slope by at most that times the
stretch of the lift, `lipschitzWith_liftedModel_add_sub`.

## How this meets the squiggly line

The idea used is **travel** (chapter 9) and the **kernel** (chapter 10).
Gradient descent moves through the kernel, so each direction has its own
rate. The sign rule leaves the kernel out. Clipping and rounding are
statements about how far the weights go, and the lift (chapter 11) turns
that distance into slope. By the slope sandwich (chapter 3), a model
whose lift stretches a great deal is one that runs near its data by being
steep, and it is also the model that is hardest to round (**argued**).

## What is not shown

- **Adam with memory.** Real Adam averages over past steps and adds a
  small constant to the divisor. Only the memoryless case, one coordinate,
  is proved.
- **Coordinates against directions.** Adam works on single weights.
  Chapter 18 is about directions of the kernel. The comparison is exact
  only when the two line up.
- **That low-rank training finds the fit**, and how far a subspace is from
  the full model's nearest fit.
- **Rounding a deep network.** The bound is for a model linear in its
  weights.

## Check yourself

1. A gap is 3 and `learning_rate` is 0.5. Under the sign rule, how many
   steps close it for a direction of strength 100? For strength 0.01?
2. AdamW has `decay = 0.5` and `learning_rate = 0.1` and no gradient from
   the loss. What fraction of a weight is left after 20 steps?
3. Gradients are clipped to `limit = 5` with `learning_rate = 0.2`. A fit
   is at distance 250. Can 100 steps reach it?

**Answers.** (1) Six for both: by `abs_sub_signStep` each step removes
`learning_rate = 0.5` from the gap, and the strength does not appear.
(2) By `iterate_adamWStep_of_no_gradient` it is `0.95 ^ 20`, about 0.36.
(3) No. By `norm_sum_clip_le` the weights move at most
`100 × (0.2 × 5) = 100`, and 250 needs at least `250 / 1 = 250` steps.

Previous: [22. Batches, small steps and budgets](22-batches-steps-and-budgets.md) · Next: [24. Symmetry: flat minima and normalisation](24-symmetry.md)
