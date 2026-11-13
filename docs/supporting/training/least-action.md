# The trained path as a path of least action

**Proofs:** [`DoubleDescent.lean`](../../../lean/SquigglyLine/Networks/DoubleDescent.lean), [`LeastAction.lean`](../../../lean/SquigglyLine/Supporting/Training/LeastAction.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/Training/LeastAction.lean`](../../../lean/SquigglyLine/Supporting/Training/LeastAction.lean)), **recalled**, or **open**.

## The idea

We train a network by lowering its loss, a step at a time. So what training
arrives at should be, in some sense, the cheapest route: the path of least
resistance. Physics has a name for this, the principle of least action. A ball
rolls along the path that costs least, and light takes the quickest route.

The idea has two parts that can be made exact, one for each of the two chains
in this project.

## Through training: the nearest fit

Gradient descent does not wander. At each step it moves the parameters only in
directions that change the outputs on the data. It never spends movement on a
direction that leaves every output where it was (**proved**:
`exists_iterate_gradientStep`).

That has a sharp consequence.

> Whenever gradient descent arrives at a fit, it is the fit nearest to where
> it started. No other fit could have been reached with less movement.

(**proved**: `gradientDescent_fit_is_nearest`.) So of all the parameter
settings that fit the data, training
picks the one that needed the least travel. This is the least-action statement
for the outer chain. The "action" is the distance moved in parameter space.

It also says what kind of function comes out. Least travel from a start means
the fitted function stays as close as possible to the starting function, which
is what `exists_fit_near_start` in the double-descent work already used.

## Through the layers: the evenest path

For the inner chain take the polarizers, where everything is exact. To turn
light through a fixed angle you may use any sequence of plates. Which sequence
loses the least?

Compare two plates that turn by `a` and then `b` with two plates that each
turn by the average, `(a + b) / 2`. The total turn is the same. The even pair
never loses more:

```
cos(a) × cos(b)  ≤  cos((a + b) / 2)²
```

(**proved**: `cos_mul_cos_le_cos_half_sq`.) So any uneven pair of neighbouring
turns can be improved by
evening it out. The best path is the one with no uneven pair left: every step
the same size. In the space where the vibration lives that is the path of
constant turning, the arc of a circle, which is the straightest path there is
on a circle.

So the least-loss route through the layers is the evenest one. This matches
what is reported for trained networks with skip connections: their paths get
straighter with training (**recalled**: Hosseini and Fedorenko).

## What this gives the wind tunnel picture

A trained wind tunnel would then be least-action twice over:

- its weights are the nearest ones that fit, and
- the flock moves through it by even steps, with no wasted turning.

Both say the same thing in different spaces: no movement that was not needed.

## What is not shown

- **Deep networks.** The first result is for models that are linear in their
  parameters. For a real network, gradient descent is known to favour some
  solutions over others, but "the nearest fit" is exact only in the linear
  case. **open**
- **Reaching the fit.** Gradient descent usually approaches a fit without
  landing on it exactly. The statement covers the case where it lands. With
  orthogonal features it lands in one step.
- **More than two plates at once.** The comparison is for a neighbouring pair.
  That equal steps are best among all sequences of `N` plates follows by
  repeating it, and that last step is argued here, not proved. **open**
- **That a trained network's layers do turn evenly.** That is an observation
  from the literature, not something derived here. **open**
