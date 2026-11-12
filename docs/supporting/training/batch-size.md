# Batch size and learning rate

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/Supporting/Training/BatchSize.lean` unless another file is named),
**recalled**, or **open**.

## The idea

There is a rule of thumb for training with large batches: if you make the
batch `k` times bigger, make the learning rate `k` times bigger too
(**recalled**: Goyal et al. 2017, the linear scaling rule). It works up to a
point and then stops working.

For a model that is linear in its weights the rule and its limit come out of
one identity.

## Two small steps against one big step

Take two batches of data. Compare two ways of using them.

- **One big step:** work out the push from both batches at the current
  weights, and take one step.
- **Two small steps:** take a step on the first batch, then a step on the
  second from where that left you.

They are nearly the same. The exact difference is one term:

```
two small steps  =  one big step  −  η² × (second batch's view of what the first step changed)
```

(**proved**: `gradientStep_two_batches`.) The first step moved the weights,
so by the time the second batch is used, its errors have shifted a little.
The shift goes through the kernel between the two batches: how alike the
model finds the inputs of one batch and the inputs of the other.

## The rule

With the usual convention the push from a batch is averaged over the batch.
Then two steps on batches of size `B` with learning rate `η` are, up to the
correction term, one step on the batch of size `2B` with learning rate `2η`
(**proved**: `linear_scaling_rule`).

That is the rule: double the batch, double the learning rate, and each
example has the same effect as before.

## Where the rule stops

The correction is of size `η²`, and the rule ignores it. So the rule is good
while `η` is small, and it fails as `η` grows.

It also has a hard ceiling. By `edge-of-stability.md` a step is stable only
while the learning rate is below `2 / sharpness`. Scaling the learning rate
up with the batch must stop there.

## When the rule is exact

If the model sees no input of one batch as like any input of the other, the
correction is zero, and two small steps equal one big step exactly
(**proved**: `two_batches_of_cross_kernel_eq_zero`).

So the two ways differ only through what the batches have in common. This is
the same cross kernel that set how much a new task makes the model forget in
`docs/supporting/new-inputs/forgetting.md`. A step on one batch is a small act of forgetting and of
generalising for the other.

## How this meets the squiggly line

A squigglier model ties fewer inputs together: its kernel between far-apart
inputs is small. For such a model batches interfere less, and small steps and
big steps agree more closely.

## What is not shown

- **The noise.** Small batches make the path of training jitter, and the size
  of the jitter is reported to go as learning rate over batch size
  (**recalled**: Smith et al. 2018). That needs batches chosen by chance,
  which is not modelled here. **open**
- **More than two batches.** The identity is for two. Repeating it gives the
  general case, with one correction term for each pair, and that is not
  written out.
- **Deep networks.** The kernel is fixed. **open**
