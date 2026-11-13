# Nearness in use: neighbours, k-means, contrastive learning

**Proofs:** [`Averaging.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean), [`Neighbours.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Neighbours.lean).

Notes from 14 Nov 2026. Each statement is marked **proved**, **argued**,
**recalled** or **open**.

## The idea

The theorem of this project is about the distance from the data to a line.
Three common methods work with distance directly and with nothing else:
copying the label of the nearest example, grouping points round their
nearest centre, and scoring pairs by how near they are.

## Three methods

Proofs in
[`lean/SquigglyLine/Supporting/NewInputs/Neighbours.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Neighbours.lean).

Three common methods use nothing but the distance between points.

- **Nearest neighbours.** To label a new input, copy the label of the
  nearest training input. If the truth has slope at most `K`, the answer is
  wrong by at most `K` times the distance to that input (**proved**:
  `abs_sub_nearest_le`). This is the theorem of this project read the other
  way: how far the data is from the query, times slope, is the error.
- **k-means.** The cost is the summed squared distance from each point to
  its centre. A step has two halves. Give every point a centre no further
  than the one it had, and the cost does not rise (**proved**:
  `sum_sq_reassign_le`). Move a centre to the mean of its points, and no
  other place for it has a lower cost (**proved**: `sum_sq_mean_le`, from
  `weightedMean_isBest`). So the cost never rises. Vector quantisation is
  the first half used as a layer.
- **Contrastive learning.** The loss is a softmax over the cosine
  similarity of a query with each key, divided by a temperature `τ`. For
  vectors of length one, the dot product is one minus half the squared
  distance (**proved**: `inner_eq_one_sub_of_unit`), and adding the same
  number to every score changes no share (**proved**: `softmax_add_const`).
  So the shares are those of a softmax over minus the squared distance,
  divided by `2τ` (**proved**: `softmax_cosine_eq_softmax_distance`). Those
  are the shares of the ideal denoiser above, with noise level `√τ`. A
  contrastive loss scores pairs by nearness, and its temperature is a
  width.

## How this meets the squiggly line

Through **nearness** and **slope**. The nearest-neighbour bound is the
slope sandwich used as a method: distance to the data, times slope, is the
error. The contrastive loss shows that a softmax over similarity is a
softmax over distance, so its temperature is a width, as in
`docs/networks/radial-basis.md`.

## What is not shown

- **That k-means stops.** Only that its cost never rises.
- **What the contrastive loss does to the lift as it trains.** **open**
- **Nearest neighbours with noisy labels**, where the classical result
  compares its error with the best possible (**recalled**: Cover and Hart
  1967).
