# Rules for the step: Adam, clipping, low-rank training and rounding

**Proofs:** [`LinearModel.lean`](../../../lean/SquigglyLine/Networks/LinearModel.lean), [`NetworkSlope.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean), [`StepRules.lean`](../../../lean/SquigglyLine/Supporting/Training/StepRules.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/Training/StepRules.lean`](../../../lean/SquigglyLine/Supporting/Training/StepRules.lean) unless another file is named),
**argued**, **recalled**, or **open**.

## The idea

Every other note here trains with plain gradient descent, where the step is
in proportion to the gradient. Most networks are trained with something
else. This note takes four common rules and says what each does to travel.

## Adam

Adam divides each coordinate of the gradient by a running estimate of that
coordinate's size (**recalled**: Kingma and Ba 2015). Take the simplest case,
with no memory of earlier steps. The estimate is then the size of the
present gradient, and:

- the step is the sign of the gradient (**proved**: `adamStep_eq_sign`);
- multiplying the loss by a positive number changes nothing (**proved**:
  `adamStep_mul`);
- every coordinate with a gradient moves the same distance (**proved**:
  `abs_adamStep`).

Set this beside `docs/supporting/training/spectral-bias.md`. Under plain
gradient descent the error along a direction of strength `λ` shrinks by the
factor `1 − ηλ` per step. Strong directions are learned first and weak ones
wait. Under the sign rule a gap of `d` closes by `η` per step and takes
`|d| / η` steps, whatever the strength (**proved**: `abs_sub_signStep`).

So Adam takes away the clock that makes gradient descent learn gentle
functions first. In the terms of the line: the squiggly parts of the fit,
which lie along weak directions, are no longer made to wait. That is a
reason Adam trains faster, and a reason it can fit noise sooner.
(**argued** from the two proved rates)

## Gradient clipping

Clipping shortens any gradient longer than a limit `c` to length `c`, and
leaves the rest alone (**recalled**: Pascanu, Mikolov and Bengio 2013;
**proved**: `norm_clip_le`, `clip_of_norm_le`).

It is a cap on travel. After `t` steps of size `η` the weights have moved at
most `t·η·c`, whatever the gradients were (**proved**: `norm_sum_clip_le`).
A fit at distance `d` therefore cannot be reached in fewer than `d / (η·c)`
steps. Clipping is used where one bad step would throw the weights far away,
which is where the slope product of
`docs/supporting/network-shape/network-slope.md` is far above one.

## Training inside a subspace

Low-rank adaptation trains a small number of new directions and freezes the
rest (**recalled**: Hu et al. 2021). Earlier work found that many tasks can
be fitted inside a random subspace of far fewer dimensions than the model
has (**recalled**: Li et al. 2018).

Confining the weights to a subspace never shortens the trip. If a fit exists
inside the subspace, it is at least as far from the start as the nearest fit
of the full model (**proved**: `travel_le_travel_comp`). This is
`travel_coprod_le` in [`LinearModel.lean`](../../../lean/SquigglyLine/Networks/LinearModel.lean) read the other way: adding
directions never lengthens the trip, and removing them never shortens it.

So low-rank training trades travel for parameters. It works well when the
nearest fit of the full model already lies close to the subspace, which is
what "the update has low rank" means (**argued**).

## Rounding the weights

Quantisation stores each weight in a few bits (**recalled**: Courbariaux,
Bengio and David 2015, and much since). That moves the weights by a rounding
error `δ`.

For a model linear in its weights, each output moves by at most the size of
`δ` times the size of the features (**proved**:
`abs_liftedModel_add_sub_le`), and the slope changes by at most the size of
`δ` times the stretch of the lift (**proved**:
`lipschitzWith_liftedModel_add_sub`).

So rounding is a small forced trip in weight space, and the damage is that
trip times the stretch. A model whose lift stretches a lot is a model that is
hard to round. By the slope sandwich that is a model whose line runs near
its data by being steep. (**argued**)

## What is not shown

- **Adam with memory.** Real Adam averages over past steps and adds a small
  constant to the divisor. Only the memoryless case is proved.
- **Coordinates against directions.** Adam works on single weights. Spectral
  bias is about directions of the kernel. The comparison is exact only when
  the two line up.
- **That low-rank training finds the fit**, and how far the subspace is from
  the full model's nearest fit.
- **Rounding a deep network.** The bound is for a model linear in its
  weights. Through several layers the error is multiplied by the slope of
  the layers after it (**argued** from [`NetworkSlope.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean)).
