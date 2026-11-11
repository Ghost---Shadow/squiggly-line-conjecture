# Mode connectivity: when two fits are joined by a straight line

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/ModeConnectivity.lean`), **recalled**, or **open**.

## The idea

Train the same network twice from different starts. You get two sets of
weights that both fit. Walk in a straight line from one to the other. Often
the loss rises on the way: there is a hill between them. But it is reported
that the two can be joined by a curved path with no hill
(**recalled**: Garipov et al. 2018; Draxler et al. 2018), and that after
relabelling the neurons of one network, even the straight line has no hill
(**recalled**: Entezari et al. 2022; Ainsworth et al. 2023, "Git Re-Basin").
That last claim is a conjecture.

Two exact statements sit under this. One says where there is no hill. The
other shows the smallest hill there is, and what removes it.

## No hill for a model that is linear in its weights

Take a model that is linear in its weights and any two settings of the
weights. On the straight line between them the error is a blend of the two
errors: at a fraction `t` of the way it is `(1 − t)` of the first plus `t` of
the second (**proved**: `residual_along_between`).

So:

- **The line between two fits is all fits.** Every point on it fits the data
  exactly (**proved**: `fit_along`).
- **There is never a hill.** Anywhere on the line, the error is no larger than
  the larger of the two ends (**proved**: `no_barrier`).

For such a model the fits form one flat sheet. There is one valley.

## The smallest hill: two weights multiplied

Now the smallest model that has depth: one input weight `a` times one output
weight `b`. Its output is `a × b`. Take two fits of the same target `y`, and
walk the straight line between them. Partway along, the output is off by
exactly

```
t (1 − t) × (a₁ − a₂) × (b₁ − b₂)
```

(**proved**: `twoLayer_along`.) The hill is the product of how much the two
fits differ in each weight. It is zero only when they agree in one of them.

The worst case is a fit and its mirror image. If `(a, b)` fits, so does
`(−a, −b)`, because the two signs cancel (**proved**: `twoLayer_flip`). Halfway
between them both weights are zero and the output is zero, whatever the target
was (**proved**: `twoLayer_midpoint_mirror`). The whole target is lost.

But the mirror image is the same function. Flip its signs back and the two
fits are the same point, and there is no line to walk. The hill came entirely
from writing one function in two ways.

## What this says about the conjecture

In a real network the relabelling is a shuffle of neurons, not a flip of
signs, but it plays the same part. Two networks may compute nearly the same
thing with their neurons in a different order. The straight line between them
then mixes unlike neurons and the loss rises. Line the neurons up first and
the hill may go. The two-weight model shows this happening exactly. That it
always happens for wide networks is the conjecture, and it stays **open**.

## How this meets the squiggly line

Depth is what made the model squiggly, and depth is what made the hill: the
hill is a product of two differences, and a product only appears when weights
multiply. Width without depth gives one flat valley. So the same thing that
lets a network bend also splits its fits into separate valleys.

## What is not shown

- **Real networks.** The no-hill result is for models linear in their weights.
  The hill is shown for two weights. **open**
- **That shuffling neurons removes the hill.** Shown here only for the sign
  flip of the two-weight model. **open**
- **Curved paths.** That fits of a deep network can be joined by a curved path
  with no hill is not addressed. **open**
