# The edge of stability

**Proofs:** [`EdgeOfStability.lean`](../../../lean/SquigglyLine/Supporting/Training/EdgeOfStability.lean), [`SpectralBias.lean`](../../../lean/SquigglyLine/Supporting/Training/SpectralBias.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/Training/EdgeOfStability.lean`](../../../lean/SquigglyLine/Supporting/Training/EdgeOfStability.lean) unless another file is named),
**recalled**, or **open**.

## The idea

Train a network with plain gradient descent and watch how sharp the loss is in
its sharpest direction. Two things are reported. The sharpness climbs during
training. Then it stops at about `2 / step size` and hovers there, while the
loss keeps going down in a jumpy way (**recalled**: Cohen et al. 2021,
"Gradient Descent on Neural Networks Typically Occurs at the Edge of
Stability").

Why that number? For a model that is linear in its weights the number `2` is
exact, and it comes from the same line of algebra as spectral bias.

## One direction, three fates

Follow a direction of the labels of strength `λ`. The strength is the
sharpness of the loss in that direction. Each step multiplies the error along
it by `1 − ηλ`, where `η` is the step size (**proved** earlier:
`inner_residual_gradientStep` in [`SpectralBias.lean`](../../../lean/SquigglyLine/Supporting/Training/SpectralBias.lean)). So the size of the
error is multiplied by `|1 − ηλ|` each step
(**proved**: `abs_inner_residual_iterate_gradientStep`).

Everything turns on whether that number is below one.

- **Below the edge, `ηλ < 2`.** The number is below one and the error shrinks
  at every step (**proved**: `shrinks_below_edge`).
- **On the edge, `ηλ = 2`.** The number is exactly one. The error flips sign
  at every step and keeps its size for ever
  (**proved**: `holds_at_edge`).
- **Past the edge, `ηλ > 2`.** The number is above one. The error grows at
  every step, at least as fast as `1 + t(ηλ − 2)` after `t` steps, so without
  limit (**proved**: `grows_past_edge`).

Put another way: a direction is stable exactly when the step size is below
`2 / λ` (**proved**: `stable_iff_lt_two_div`). The sharpest direction has the
largest `λ`, so it sets the largest step that training can take.

## What this explains, and what it does not

It explains the number. `2 / step size` is where the sharpest direction stops
shrinking and starts to grow. A model cannot sit past it. It also explains the
jumpy loss: on the edge the error in the sharpest direction swings from one
side to the other without dying down.

It does not explain the climb. In a model that is linear in its weights the
sharpness never changes, so nothing here says why a real network's sharpness
rises to the edge. And it does not explain the hovering. Past the edge a
linear model blows up. A real network is pulled back. Both need a kernel that
changes as the weights move. **open**

## How this meets the squiggly line

`flat-minima.md` showed that rescaling the parameters by `c` is the same as
dividing the step size by `c²`. So the edge is not a fact about the function.
It is a fact about the step size measured against the sharpness, and their
product `ηλ` is what rescaling leaves alone. A squigglier model has stronger
directions, so for a fixed step size it sits nearer the edge.

## What is not shown

- **Why sharpness rises during training.** **open**
- **Why training survives at the edge.** **open**
- **Mini-batches and momentum.** The edge moves when the method changes. Only
  plain gradient descent is covered.
