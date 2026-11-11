# The information bottleneck, by counting

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/Bottleneck.lean` unless another file is named),
**recalled**, or **open**.

## The idea

The information bottleneck view says a deep network does two things as data
passes through its layers. It throws away what the input says that the label
does not need, and it keeps what the label does need
(**recalled**: Tishby and Zaslavsky 2015). Whether real networks do compress
in this way during training is disputed (**recalled**: Saxe et al. 2018).

The usual statement is in terms of mutual information, which is hard to
measure in a network. There is a plainer version that needs only counting, and
it fits the flock of birds exactly.

## Counting places

Send a finite flock of inputs through the layers. After each layer, count how
many different places the flock occupies. Two birds at the same place can
never be told apart again (**proved** earlier: `merged_stays_merged` in
`MarkovChains.lean`). The count is the plainest measure of how much the layer
still knows about which input it was given.

Three facts pin the count down.

- **It never goes up.** A later layer cannot occupy more places than an
  earlier one (**proved** earlier: `card_image_runLayers_append_le`).
- **It starts no higher than the flock.** There are no more places than birds.
- **It never goes below the number of labels.** If the network gets every
  label in the flock right, then at every layer there are at least as many
  places as there are different labels
  (**proved**: `card_image_label_le`).

Together:

```
number of labels  ≤  places after any layer  ≤  number of inputs
```

(**proved**: `bottleneck`.) The count slides down between these two walls as
the data goes deeper. That is the bottleneck.

## Why it cannot go lower

If two inputs with different labels land on the same place at some layer, they
stay together, so they get the same answer, so one of them is wrong. A network
that is right on both must keep them apart at every layer
(**proved**: `label_eq_of_merged`).

## What full compression means

Suppose a layer has squeezed all the way: it has exactly as many places as
there are labels. Then two inputs share a place at that layer exactly when
they share a label (**proved**: `merged_iff_label_eq`).

Such a layer knows the label and nothing else about the input. That is the
ideal the bottleneck view describes: everything the label does not need is
gone, and nothing it needs is lost.

## How this meets the squiggly line

In the wind tunnel a layer that merges birds is a pigeon coop: black birds in
one, white in another. This note says what the coops are allowed to do. They
may merge birds of one colour. They may never merge birds of two colours. And
the fewest coops that can work is one for each colour.

## What is not shown

- **Counting is not Shannon information.** The count ignores how many birds
  sit at each place. The usual bottleneck weighs places by how likely they
  are. **open**
- **Noise.** Layers here are exact functions. With noise, two nearby places
  may be as good as merged, which the count does not see. **open**
- **That training compresses.** Nothing here says gradient descent moves a
  network towards the lower wall. That is the disputed part. **open**
