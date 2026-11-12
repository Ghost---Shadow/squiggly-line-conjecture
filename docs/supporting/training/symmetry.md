# Symmetries: changes to the weights that leave the line alone

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/Supporting/Training/Symmetry.lean` unless another file is named),
**argued**, **recalled**, or **open**.

## The idea

Travel is measured in weight space. The line lives in function space. The two
do not match one to one: many settings of the weights draw the same line.
A change to the weights that leaves the line alone is called a symmetry.

Along a symmetry the loss has no slope, so training does not move that way.
It moves at right angles. `docs/supporting/training/flat-minima.md` used one
symmetry to show that flatness can be changed without changing the function.
This note takes three symmetries and reads off what each does to training.

## Normalisation: rescaling everything

Batch normalisation and layer normalisation divide a layer's output by its
own size (**recalled**: Ioffe and Szegedy 2015; Ba, Kiros and Hinton 2016).
So multiplying all the weights that feed the layer by a positive number
changes nothing downstream. The loss is the same.

For any loss with that property:

- The gradient is at right angles to the weights (**proved**:
  `inner_gradient_self_eq_zero`).
- So a gradient step of size `η` adds `η²·‖gradient‖²` to the squared size of
  the weights (**proved**: `norm_sq_sub_smul_of_inner_eq_zero`).
- The weights never get shorter (**proved**: `norm_le_norm_sub_smul`).

Two things follow for the squiggly line.

**The size of the weights stops meaning slope.** Without normalisation, the
slope of a layer is at most the size of its weights
(`docs/supporting/network-shape/network-slope.md`). With it, the weights can
be any size and draw the same line. So "small weights, gentle line" no longer
holds for these layers, and weight decay on them does not limit slope
directly.

**What weight decay does there is set the step size.** The weights grow with
every step. The same step then turns them through a smaller angle. Weight
decay pulls them back and keeps the angle from shrinking (**argued**;
**recalled**: van Laarhoven 2017; Hoffer et al. 2018).

## Deep linear networks: rescaling one layer against the next

Take the smallest network with depth: two weights multiplied, `a·b`. Doubling
`a` and halving `b` leaves the product alone.

One gradient step changes `a² − b²` by the factor `1 − η²·(a·b − y)²`
(**proved**: `balance_after_step`). For a small step that is almost no change
at all. So:

- layers of equal size stay of equal size (**proved**:
  `balanced_stays_balanced`), and
- each then carries the same share of the slope: `|a| = |b|` (**proved**:
  `abs_eq_abs_of_balanced`).

Training does not let one layer take all the slope while the other sits near
zero, unless it started that way. This is the conservation law behind the
theory of deep linear networks (**recalled**: Saxe, McClelland and Ganguli
2014; Arora, Cohen and Hazan 2018). It is also why the product of the layer
sizes in the slope bound is spread evenly over the layers in practice
(**argued**).

## Relabelling the hidden units

Shuffle the units of a hidden layer, taking each unit's incoming and outgoing
weights along with it. The function is the same (**proved**:
`oneHiddenLayer_relabel`).

So every fit comes in as many copies as there are ways to shuffle the units.
Two trained networks may sit far apart in weight space only because their
units are numbered differently. The travel that matters is to the nearest
copy (**argued**). The conjecture that two trained networks have no hill
between them once their units are matched up (**recalled**: Entezari et al.
2022) is a statement about that nearest copy. It is open, and listed in
`docs/wishlist.md`.

## How this meets the squiggly line

The theorem ties nearness to slope, and slope is a property of the line.
Travel is a property of the weights. Symmetries are the gap between the two.
Each result above says how training behaves in that gap: it does not move
along it, it drifts outward across it, or it holds a balance fixed.

## What is not shown

- **Normalisation over a batch.** The proofs use only that the loss does not
  change under rescaling. What batch statistics do beyond that is open
  (`docs/open-problems.md`, item 21).
- **The effective step size.** That the angle turned shrinks as the weights
  grow is argued, not proved.
- **More than two layers, and matrices.** The balance law is proved for two
  numbers.
- **No hill after matching units.** Open.
