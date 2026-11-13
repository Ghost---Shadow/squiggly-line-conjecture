# Squiggly below, flat above: the kernel trick

**Proofs:** [`FourierLift.lean`](../../lean/SquigglyLine/Networks/FourierLift.lean), [`Lift.lean`](../../lean/SquigglyLine/Networks/Lift.lean), [`Capacity.lean`](../../lean/SquigglyLine/Supporting/NetworkShape/Capacity.lean), [`CrossEntropy.lean`](../../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean), [`LeastAction.lean`](../../lean/SquigglyLine/Supporting/Training/LeastAction.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Networks/Lift.lean`](../../lean/SquigglyLine/Networks/Lift.lean) unless another file is named),
**argued**, **recalled**, or **open**.

## The question

Is a squiggly line in few dimensions the same thing as a flat plane in many?

For every model that is linear in its weights the answer is yes, exactly.
There is one catch, given at the end.

## The lift

Such a model works in two moves.

- **Lift.** Send the input `x` to a list of features `φ(x)`. The list is
  usually much longer than the input. For the Fourier model the features are
  `cos(πx), sin(πx), cos(2πx), sin(2πx), …`.
- **Weigh.** Multiply each feature by its weight and add up.

The second move is a flat function of the features: its value at a blend of
two feature lists is the same blend of the two values (**proved**:
`flatModel_blend`). Its graph is a flat plane in the space of features, which
this note calls upstairs.

The model is that flat function after the lift (**proved**:
`liftedModel_eq_comp`). So:

> A point is on the squiggly line downstairs exactly when its lift is on the
> flat plane upstairs.

(**proved**: `embed_mem_curve_liftedModel_iff`.) The same holds for a
classifier. The inputs it scores zero form a squiggly boundary downstairs, and
their lifts lie on a flat plane through the origin upstairs (**proved**:
`boundary_eq_preimage`). This is the picture behind support vector machines
(**recalled**: Boser, Guyon and Vapnik 1992).

One sine wave shows it. The lift `x ↦ (cos wx, sin wx)` winds the input round
a circle. A flat plane over that circle, cut along the circle and unrolled, is
the wave `a·cos(wx) + b·sin(wx)`.

## Where the squiggle is

The plane is flat, so the squiggle is all in the lift. The plane only has a
tilt, which is the size of the weights.

If the lift stretches distances by at most `K`, the line is no steeper than
the size of the weights times `K` (**proved**: `lipschitzWith_liftedModel`).

```
slope of the line  ≤  tilt of the plane × stretch of the lift
```

The slope sandwich of the theorem then reads in those two numbers. The line
can be nearer to a data point than its vertical error only by the factor
`√(1 + (tilt × stretch)²)` (**proved**: `verticalDist_liftedModel_le`).

So there are two ways to buy a squigglier line: a lift that stretches more,
or bigger weights. Raising the frequency of the Fourier features is the
first. Training is the second, and it is what travel measures.

## The kernel trick

Training moves the weights only along the lifted data points
(`exists_iterate_gradientStep` in [`LeastAction.lean`](../../lean/SquigglyLine/Supporting/Training/LeastAction.lean), and
`exists_iterate_errorStep` in [`CrossEntropy.lean`](../../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean) for any loss). Weights of
that kind predict at a new input by

```
old prediction + Σ cᵢ × kernel(data point i, new input)
```

where the kernel of two inputs is the overlap of their lifts (**proved**:
`liftedModel_add_sum`). The lift itself is never needed, only the kernel. That
is the kernel trick: the plane upstairs can have any number of dimensions,
even infinitely many, and the work stays downstairs.

A kernel that comes from a lift is symmetric, and summed over all pairs of
data points with any weights it is never negative, because the sum is the
squared length of a vector upstairs (**proved**: `liftKernel_comm`,
`sum_sum_liftKernel_nonneg`). The converse, that every such kernel comes from
some lift, is a known theorem (**recalled**: Mercer, Moore and Aronszajn) and
is not proved here.

## The catch

Any function at all is flat in some lift: take the function itself as the one
feature (**proved**: `exists_lift_eq`). So "it is flat upstairs" says nothing
unless the lift is fixed before the labels are seen.

With a fixed lift into `m` dimensions, the model can match arbitrary labels
on at most `m` points (`exists_unfittable` in [`Capacity.lean`](../../lean/SquigglyLine/Supporting/NetworkShape/Capacity.lean)). That is the
real content: a fixed lift buys a fixed amount of squiggle.

## What this says about networks

The last layer of any network is a flat plane over a lift, and the lift is
everything before the last layer (**argued**: it is the definition of a last
linear layer).

- If the earlier layers are frozen, the lift is fixed and all of this
  applies as it stands.
- If the network is very wide and trained gently, the lift barely moves and
  it applies approximately (**recalled**: Jacot et al. 2018).
- Otherwise the lift moves during training. The network is then choosing its
  own upstairs, which is what "learning features" means. Nothing here covers
  that. **open**

## What is not shown

- **A lift that moves.** See above.
- **The converse for kernels.** Recalled, not proved.
- **The sine wave picture** is now in [`FourierLift.lean`](../../lean/SquigglyLine/Networks/FourierLift.lean); see
  `docs/networks/fourier-lift.md`.
- **How much stretch a given lift has.** For the Fourier lift of one
  frequency `w` it is at most `w` (`lipschitzWith_fourierLift`). Other lifts
  are not computed.
