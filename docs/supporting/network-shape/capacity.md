# Storage capacity: what a network can memorise

**Proofs:** [`Depth.lean`](../../../lean/SquigglyLine/Networks/Depth.lean), [`Capacity.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/Capacity.lean), [`DepthSeparation.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/DepthSeparation.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/NetworkShape/Capacity.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/Capacity.lean) unless another file is named),
**recalled**, or **open**.

## The idea

How much can a network store? The question is old. A single neuron with `N`
inputs can store about `2N` random yes-or-no answers
(**recalled**: Cover 1965; Gardner 1988). Big modern networks can memorise
their whole training set, even with random labels (**recalled**: Zhang et al.
2017). The rough rule is that capacity goes with the number of parameters.

"Store" here means the hard case: labels with no pattern, so there is nothing
to learn and everything must be remembered. Three counts bound it, and each
is short.

## One parameter for each stored number

Take a model that is linear in its weights, with `m` weights. If it can fit
every possible set of labels on its data points, there are at most `m` data
points (**proved**: `finrank_le_of_fits_all`). With more points than weights,
some set of labels cannot be fitted, whatever the weights
(**proved**: `exists_unfittable`).

This is the threshold in the travel table: 20 points, and no fit until there
are 20 parameters. It is also where double descent has its peak. At the
threshold the model has exactly enough room and none to spare.

## One bit for each stored bit

Now let the weights be anything at all, but written down in `b` bits. Then
there are at most `2^b` settings of the weights, so the network computes at
most `2^b` different functions. To memorise every yes-or-no labelling of `n`
inputs it must compute `2^n` different functions on them. So `n ≤ b`
(**proved**: `card_le_bits_of_memorises`).

No design of network gets around this. A network cannot store more bits than
it is made of.

## One unit for each turn

For a ReLU network with one hidden layer there is a third count. Labels that
alternate along a line, low, high, low, high, need a unit for every
up-and-down (**proved** earlier: `card_ge_of_zigzag` in
[`DepthSeparation.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/DepthSeparation.lean)). So `m` units can follow at most about `m` turns.

## Depth buys pattern, not storage

A stack of `L` folds draws `2^L` turns with only `2L` neurons (**proved**
earlier: `iterate_tent_dyadic`). That looks like storing `2^L` answers in
`2L` neurons. It is not. The stack draws one particular pattern, the same
zigzag at every scale. It cannot be set to an arbitrary pattern of that
length, because by the count of bits it does not hold enough bits.

So the two things a network does are separate:

- **Storing** arbitrary answers costs one parameter, or one bit, for each.
  Depth does not help.
- **Expressing** a pattern with structure can be exponentially cheaper with
  depth.

A network generalises when its data has the second kind of regularity and it
is forced to use it. It memorises when it has the room and nothing stops it.

## How this meets the squiggly line

A squiggly curve passes near every point, and it is tempting to read that as
"it can fit anything". The counts say otherwise. Passing near points is about
where the curve goes. Fitting chosen labels at chosen inputs is about how many
free numbers the curve has. The tent curve passes within `1 / 2^L` of every
point and has only `2L` neurons to set.

## What is not shown

- **Networks that are not linear in their weights, with exact real weights.**
  The first count is for models linear in their weights and the second needs
  weights of finite precision. For ReLU networks with real weights the known
  bounds are of the order of weights times layers (**recalled**: Bartlett et
  al. 2019). **open** here.
- **Random labels are the worst case.** Capacity for labels with structure is
  a different and harder question. **open**
- **Associative memories.** The capacity of a Hopfield network is not
  addressed.
