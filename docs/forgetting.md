# Catastrophic forgetting: what a new task costs an old one

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/Forgetting.lean` unless another file is named),
**recalled**, or **open**.

## The idea

Train a network on one task, then on another. It often loses the first. This
is called catastrophic forgetting, and it has been known for a long time
(**recalled**: McCloskey and Cohen 1989; French 1999). The usual remedies
protect the weights the old task relied on
(**recalled**: Kirkpatrick et al. 2017).

How much is forgotten, and when is nothing forgotten? For a model that is
linear in its weights both have exact answers.

## One step on the new task

There is one set of weights and two tasks. Each task has its own inputs and
labels. A gradient step on the new task moves the weights, and that changes
the outputs on the old task as well.

By how much? The old task's errors change by the step size times the new
task's errors, passed through the table of likeness between the old inputs and
the new ones (**proved**: `residual_gradientStep_other`). Call that table the
cross kernel. Read along one direction `u` of the old labels:

```
change in old error along u  =  − η × (how the new task sees u) matched against the new errors
```

(**proved**: `inner_forgetting_step`.) The weights do not appear. Only the
cross kernel does.

So forgetting is interference. A step that corrects the new task's answer at a
new input also shifts the answer at every old input the model thinks is like
it. If the old label there disagrees, the old task gets worse.

## When nothing is forgotten

If the cross kernel is zero, the model sees no old input as like any new one.
Then training on the new task, for any number of steps, leaves every old error
exactly where it was (**proved**: `residual_iterate_of_cross_kernel_eq_zero`).

That is the exact form of "the tasks use separate features".

## A ceiling on forgetting

Moving the weights a certain distance changes the old outputs by at most that
distance times the size of the old task's features
(**proved**: `forgetting_le_dist`).

Gradient descent moves the weights as little as any method could: if it
arrives at a fit of the new task, that fit is the nearest one (**proved**
earlier: `gradientDescent_fit_is_nearest` in `LeastAction.lean`). Together:

> The amount forgotten is at most the size of the old task's features times
> the distance from the start to the nearest fit of the new task.

(**proved**: `forgetting_le_travel`.) The new task's travel is the budget.
Forgetting cannot spend more than that.

## How this meets the squiggly line

The squiggly line theorem is about travel: a squigglier model starts nearer to
a fit. Here travel turns up as the ceiling on forgetting. A new task that the
model is already close to costs the old task little, because there is little
distance to move.

It also joins `same-kernel.md`. There a step changed a test prediction through
the test row of the kernel. Here the old task is the test set. Forgetting and
generalising are one mechanism: a step on one input moves the answer on every
input the kernel ties to it. When the labels agree that is generalisation.
When they disagree it is forgetting.

## What is not shown

- **Deep networks.** The cross kernel of a deep network changes while it
  trains on the new task. **open**
- **Whether more parameters help.** More parameters shorten the travel but can
  also enlarge the old task's features. Which wins is not settled here.
  **open**
- **The remedies.** Replay, frozen weights and penalties on important weights
  are not modelled. **open**
