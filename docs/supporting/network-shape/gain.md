# A gain per step: He initialisation and the Bellman update

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/Supporting/NetworkShape/Gain.lean` unless another file is named),
**argued**, **recalled**, or **open**.

## The idea

`docs/supporting/network-shape/vanishing-gradients.md` shows that a gain of
`g` per layer becomes `g^L` after `L` layers. Below one it dies out, above
one it blows up. Two well-known designs are choices of that gain. One wants
it to be exactly one. The other wants it below one.

## He initialisation: a gain of one through a fold

A ReLU keeps the positive part of its input and drops the rest. The squared
size of what it keeps, and of what it would have kept of the mirror image,
add up to the squared size of the input (**proved**:
`relu_sq_add_relu_neg_sq`).

So if the input is as often negative as positive, the fold keeps exactly half
of its mean squared size (**proved**: `integral_relu_sq_of_symmetric`).

A unit adds up `n` inputs, each through a random weight. If the weights have
variance `2 / n`, the factor `n × 2/n × 1/2` is one (**proved**: `he_gain`).
The half lost in the fold is made up, and the signal keeps its size from
layer to layer. That is the rule known as He initialisation (**recalled**:
He et al. 2015; Glorot and Bengio 2010 for the version without the fold).

In the terms of this repository: a fold is how depth makes squiggle
(`Depth.lean`), and every fold costs half the signal. He initialisation is
the weight scale at which a network can stack folds without the signal dying
or blowing up. It is the middle case of `VanishingGradients.lean`.

## The Bellman update: a gain below one on purpose

Reinforcement learning keeps a guess at the value of each state: the reward
to come, with later rewards counted for less by a discount `γ` below one. One
sweep of updates replaces each value by the reward now, plus `γ` times the
average value of where you go next (**recalled**: Bellman 1957).

A sweep has slope at most `γ`. Two different guesses, after one sweep, differ
by at most `γ` times what they did, measured by their largest disagreement
(**proved**: `lipschitzWith_bellman`). After `n` sweeps the factor is `γ^n`
(**proved**: `dist_iterate_bellman_le`).

So every starting guess is pulled to the same answer. Here a gain below one
is the point. The update forgets where it started, at the rate that
`VanishingGradients.lean` gives for a signal dying out.

The slope is in the space of value tables, not in the input. The link to the
squiggly line is the same rule read on a different map: a product of slopes
below one loses the starting point, and a product of one keeps it.

## What is not shown

- **Symmetry of the signal** is assumed, not derived. For a random first
  layer on centred inputs it holds (**argued**).
- **Independence across units** behind "variance adds" is recalled.
- **The best action.** The update here follows a fixed way of acting.
  Choosing the best action at each state gives the same slope bound
  (**recalled**), and is not proved here.
- **Value updates with a network** in place of a table. The network's own
  slope then enters, and the bound can fail (**recalled**: the "deadly
  triad"). **open** here.
