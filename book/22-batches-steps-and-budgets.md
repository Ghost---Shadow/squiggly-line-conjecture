# 22. Batches, small steps and budgets

**In the repository:**
[`BatchSize.lean`](../lean/SquigglyLine/Supporting/Training/BatchSize.lean),
[`SmallSteps.lean`](../lean/SquigglyLine/Supporting/Training/SmallSteps.lean),
[`ComputeBudget.lean`](../lean/SquigglyLine/Supporting/Training/ComputeBudget.lean),
notes [`batch-size.md`](../docs/supporting/training/batch-size.md),
[`small-steps.md`](../docs/supporting/training/small-steps.md) and
[`compute-budget.md`](../docs/supporting/training/compute-budget.md).
**You need:** chapters 10, 12 and 13.

## The idea

Three rules of practice are about how to spend training. Make the batch
`factor` times bigger and the learning rate `factor` times bigger (**recalled**:
Goyal et al. 2017). Cut one big jump into many small ones, as diffusion
and annealing do. Split a fixed compute budget between model size and
data. Each has a short proof for a simple model.

> Two small steps on two batches equal one big step on both, minus a term
> of size `learning_rate²`. Many steps cost less when each step's cost
> grows as the square of its size. Under a fixed budget, the loss is
> smallest when the two terms of the loss are equal.

## An example you can do by hand

**Batches.** One weight, starting at 0, with `learning_rate = 0.1`. Batch
one has feature 1 and label 1. Batch two has feature 1 and label 3.
Two small steps: the first residual is 1, so the weight becomes 0.1. The
second residual is `3 − 0.1 = 2.9`, so the weight becomes
`0.1 + 0.1 × 2.9 = 0.39`. One big step: `0.1 × (1 + 3) = 0.4`. The gap is
0.01, which is `0.1² × 1 × 1 × 1`, the learning rate squared times the
cross term.

**Steps.** A step of size `step_size` costs `step_size²`. Cover distance 1. One step costs
1. Ten steps of size 0.1 cost `10 × 0.01 = 0.1`. If the cost were the step size itself,
ten steps would cost `10 × 0.1 = 1`, no better than one.

**Budget.** Let `param_cost = 8` and `data_cost = 2`, and spend 100 units
of `param_count × data_count`. At 20 parameters and 5 data the terms are
`8 / 20 = 0.4` and `2 / 5 = 0.4`: balanced, loss above the floor 0.8. At
10 and 10 the loss is `0.8 + 0.2 = 1.0`, and at 40 and 2.5 it is
`0.2 + 0.8 = 1.0`. Both are worse.

## The statement

```lean
theorem gradientStep_two_batches
    (learning_rate : ℝ)
    (weights : Weights) :
    let first_linear_predict : LinearPredictor Weights FirstOutputs :=
      first_predict
    let second_linear_predict : LinearPredictor Weights SecondOutputs :=
      second_predict
    let two_steps :=
      TAKE_GRADIENT_STEP second_predict second_labels learning_rate
        (TAKE_GRADIENT_STEP first_predict first_labels learning_rate weights)
    let first_residual :=
      GET_RESIDUAL first_linear_predict first_labels weights
    let second_residual :=
      GET_RESIDUAL second_linear_predict second_labels weights
    let one_big_step :=
      weights + learning_rate • (adjoint first_predict first_residual
        + adjoint second_predict second_residual)
    let correction :=
      learning_rate ^ 2 •
        adjoint second_predict
          (second_predict (adjoint first_predict first_residual))  -- the first step moved the second batch's outputs
    two_steps = one_big_step - correction := by
```

*Read aloud:* a step on the first batch then a step on the second is one
step on both, minus `learning_rate²` times what the second batch sees of
the first step.

`first_predict` and `second_predict` are the two batches' features. The
correction passes through the cross kernel of chapter 10, how alike the
model finds the inputs of one batch and the other.
`two_batches_of_cross_kernel_eq_zero` says that when that is zero the two
ways are equal. `linear_scaling_rule` restates it with the push averaged
over the batch: two steps at `learning_rate` on batches of `batch_size`
are one step on `2 × batch_size` at `2 × learning_rate`, minus the same
correction.

```lean
theorem small_steps_keep
    (step_count_pos : 0 < step_count)
    {cost_rate : ℝ}
    {distance : ℝ}
    {keep : RealFunction}
    (step_keeps : ∀ step_size,
      1 - cost_rate * step_size ^ 2 ≤ keep step_size)
    (step_is_small : cost_rate * (distance / step_count) ^ 2 ≤ 1) :
    let step_size  := distance / step_count
    let guaranteed := 1 - cost_rate * distance ^ 2 / step_count
    let kept       := keep step_size ^ step_count
    guaranteed ≤ kept := by
```

*Read aloud:* if a step of size `step_size` keeps at least
`1 − cost_rate × step_size²`, then `step_count` steps together keep at
least `1 − cost_rate × distance² / step_count`.

The counting behind it is `quadratic_cost_total`. When a step costs its
size instead, `linear_cost_total` shows the total does not fall. For
polarizers, `turn_in_steps_keeps` says any angle in `plate_count` plates
keeps at least `1 − angle² / (2 × plate_count)`.

```lean
theorem balanced_is_optimal
    {param_cost data_cost : ℝ}
    {param_count data_count : ℝ}
    {balanced_param_count balanced_data_count : ℝ}
    (param_cost_nonneg : 0 ≤ param_cost)
    (data_cost_nonneg : 0 ≤ data_cost)
    (balanced_param_count_pos : 0 < balanced_param_count)
    (balanced_data_count_pos : 0 < balanced_data_count)
    (param_count_pos : 0 < param_count)
    (data_count_pos : 0 < data_count)
    (split_is_balanced :
      IS_BALANCED_SPLIT param_cost data_cost
        balanced_param_count balanced_data_count)
    (same_budget :
      balanced_param_count * balanced_data_count = param_count * data_count) :
    let balanced_loss :=
      GET_LOSS_ABOVE_FLOOR param_cost data_cost
        balanced_param_count balanced_data_count
    let other_loss :=
      GET_LOSS_ABOVE_FLOOR param_cost data_cost param_count data_count
    balanced_loss ≤ other_loss := by
```

*Read aloud:* if a split is balanced, no other split with the same
budget has a smaller loss above the floor.

`GET_LOSS_ABOVE_FLOOR` is `param_cost / param_count + data_cost /
data_count`. `IS_BALANCED_SPLIT` says the two terms are equal. The same
file shows the ratio at the best split is `param_cost / data_cost`
whatever the budget (`balanced_ratio`), and scaling both counts by one
factor keeps it balanced (`balanced_scale`).

## Why it is true

**Batches.** The first step moves the weights. So when the second batch
takes its step, its error has shifted by what the first step did to its
outputs. That shift is the kernel between the batches applied to the
first error. The proof rewrites the second step with that shifted error
and collects terms.

**Steps.** `step_count` steps each cost about `cost_rate × (distance /
step_count)²`. The total is `cost_rate × distance² / step_count`. Then
`1 − n × cost` is at most `(1 − cost)^n` (Bernoulli), which turns the
total cost into the guarantee.

**Budget.** The square of a sum is at least four times the product
(`four_mul_div_le_sq`). The product of the two terms is
`param_cost × data_cost / budget`, the same for every split. A balanced
split reaches the bound (`balanced_loss_sq`), so nothing beats it. At the
best split the loss above the floor, squared, is
`4 × param_cost × data_cost / budget`.

## What it explains

Doubling the batch and the learning rate keeps each example's effect, up
to the correction. The correction is of size `learning_rate²`, so the rule
works while the learning rate is small. It also hits the ceiling of
chapter 19: a step is stable only below `2 / sharpness`.

Small steps help exactly when the cost of a step falls faster than its
size. The note says diffusion, curricula and annealing might have that
square law. That is **argued**, not proved. The old name for the
polarizers is the quantum Zeno effect (**recalled**: Misra and Sudarshan
1977).

For a budget, the fitted loss of Hoffmann et al. 2022 (**recalled**) has a
model term and a data term. With both powers equal to one, parameters and
data should grow together: for four times the compute, double each. The
loss above the floor falls as one over the square root of the budget. The
fitted powers 0.34 and 0.28 are measurements.

## How this meets the squiggly line

Batches use the kernel and the cross kernel of chapter 10. A squigglier
model ties fewer far inputs together, so its batches interfere less. Small
steps are the polarizers of chapter 12: many small turns deliver what a
few big ones lose. In the budget, the model term is the cost of a curve
that cannot bend enough, so a squigglier target has a larger
`param_cost`, and by `balanced_ratio` wants more parameters per datum.
That last link is the note's reading.

## What is not shown

- Batches: two batches, a fixed kernel and no chance in choosing them.
  The jitter that goes as learning rate over batch size (**recalled**:
  Smith et al. 2018) is **open**.
- Steps: that diffusion, curricula or annealing have square-law steps is
  **open**. The price of running more steps is not counted.
- Budget: why loss has this form is **open**. Compute as parameters times
  data is an assumption. For unequal powers, balance in proportion to
  the powers is **recalled**, not proved.

## Check yourself

1. In the batch example, make the learning rate 0.2. What is the gap
   between two small steps and one big step?
2. A step of size `step_size` costs `3 × step_size²`. Cover distance 2 in 10 steps. What
   share is guaranteed to be kept?
3. With `param_cost = 8` and `data_cost = 2` and a budget of 400, what
   split is balanced and what is the loss above the floor?

**Answers.** (1) By `gradientStep_two_batches` the gap is
`0.2² × 1 × 1 × 1 = 0.04`. Check: the weight goes to 0.2, then
`0.2 + 0.2 × 2.8 = 0.76`, against `0.2 × 4 = 0.8`. (2) By
`small_steps_keep` it is at least `1 − 3 × 2² / 10 = −0.2`, which says
nothing yet: the steps are too few. With 100 steps it is `1 − 0.12 =
0.88`. (3) Balanced means `8 / param_count = 2 / data_count` with
`param_count × data_count = 400`. So `param_count` is four times
`data_count`, which gives `data_count = 10` and `param_count = 40`. The loss is `0.2 + 0.2 = 0.4`, and its square
0.16 is `4 × 16 / 400` as `balanced_loss_sq` says.

Previous: [21. Dropout, noise and other regularisers](21-dropout-and-noise.md) · Next: [23. Adam, AdamW and clipping](23-adam-and-clipping.md)
