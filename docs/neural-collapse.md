# Neural collapse: why the classes end up on a simplex

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/Supporting/NetworkShape/NeuralCollapse.lean` unless another file is named),
**recalled**, or **open**.

## The idea

Keep training a classifier long after it gets every training label right. Its
last layer is reported to settle into a very tidy shape
(**recalled**: Papyan, Han and Donoho 2020):

1. All the inputs of one class land on one point.
2. The points for the different classes are equally long and equally far
   apart, as far apart as they can be. That shape is called a simplex. For
   three classes it is a triangle seen from its centre.

Why that shape? Two parts of the answer are plain geometry and can be proved
without saying anything about training.

## Part one: one point for each class

This is the counting result from `information-bottleneck.md`. A layer of a
network that gets every label right has at least one place for each label. If
it has squeezed down to exactly that many, then two inputs share a place
exactly when they share a label (**proved** earlier: `merged_iff_label_eq` in
`Bottleneck.lean`). That is the first point above, in counting form.

## Part two: the simplex is as far apart as points can get

Take `K` arrows of length one, one for each class. Measure how alike two
arrows are by their overlap: `1` if they point the same way, `0` at a right
angle, `−1` if opposite.

You would like every pair to be as unlike as possible. Two arrows can be
opposite, overlap `−1`. Three cannot all be opposite to each other. How low
can every pair go at once?

> For `K` arrows of length one, if every pair has overlap at most `c`, then
> `c` is at least `−1 / (K − 1)`.

(**proved**: `neg_one_le_of_inner_le`.) No arrangement gets every pair below
`−1 / (K − 1)`. For two classes that is `−1`, for three `−1/2`, for ten `−1/9`.

The reason is one line. Add up all the arrows. The squared length of the sum
is the `K` from each arrow's own length plus the overlaps of all the pairs
(**proved**: `norm_sum_sq_eq_sum_inner`). A squared length cannot be negative,
so the overlaps cannot all be too negative.

## Part three: the best arrangement is centred

Now suppose the arrows are evenly spread: every pair has the same overlap `c`.
Then the squared length of their sum is exactly `K × (1 + (K − 1) c)`
(**proved**: `norm_sum_sq_of_equiangular`). So:

> Evenly spread arrows reach the limit `−1 / (K − 1)` exactly when they add up
> to zero.

(**proved**: `sum_eq_zero_iff_of_equiangular`.) The farthest-apart arrangement
is the one balanced around the centre. That is the simplex, and it is why the
reported shape has class points that sum to zero.

## How this meets the squiggly line

In the wind tunnel the last layers are pigeon coops: one for each colour of
bird. This note says where the coops go when there is room to choose. They go
as far from each other as they can, and that is a simplex.

It also joins the dimpled manifold note. How far a point must be pushed to
change its label depends on how far apart the class points are. The simplex
makes that distance as large as it can be for every pair at once.

## What is not shown

- **That training goes there.** This is the real claim. It is reported proved
  for simplified models where the last-layer features are free to move
  (**recalled**, not checked here). For real networks it is an observation.
  **open**
- **Why each class collapses to one point.** The counting result says what
  full compression looks like, not that training reaches it. **open**
- **The classifier's weights.** The reports also say the last layer's weights
  line up with the class points. Not addressed. **open**
