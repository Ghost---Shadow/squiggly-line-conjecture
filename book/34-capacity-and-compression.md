# 34. Capacity and compression

**In the repository:**
[`Capacity.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Capacity.lean),
[`Bottleneck.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Bottleneck.lean),
[`CodeLength.lean`](../lean/SquigglyLine/Supporting/NetworkShape/CodeLength.lean),
[`Mixtures.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Mixtures.lean),
notes [`capacity.md`](../docs/supporting/network-shape/capacity.md),
[`information-bottleneck.md`](../docs/supporting/network-shape/information-bottleneck.md) and
[`code-length.md`](../docs/supporting/network-shape/code-length.md).
**You need:** chapters 8, 9 and 14.

## The idea

People who train models know that a big enough network can memorise its
training set, even when the labels are random. They also know that a
network can learn a pattern far smaller than the data. Two questions sit
under this. How much can a network store? And how much does it have to
throw away on the way to an answer?

Both have answers that are only counting. Chapter 8 showed that a stack of
folds draws a zigzag with exponentially many turns, so it is tempting to
think depth stores exponentially much. It does not. **Storing** arbitrary
answers costs one parameter, or one bit, for each. **Expressing** a
pattern with structure can be far cheaper.

> To memorise every possible set of labels, a model needs one weight for
> each data point, and a network needs one bit of weights for each answer.

## An example you can do by hand

Take 20 data points and a model that is linear in its weights, with 19
weights. Some set of 20 labels cannot be fitted, whatever the weights.
Give it a 20th weight and every set of labels can be fitted, if the
features are independent enough. This is the threshold of chapter 10, where
the travel peaked.

Now count bits. A network whose weights are written in 10 bits has at most
`2 ^ 10 = 1024` settings. To memorise every yes-or-no labelling of 11
inputs it would need `2 ^ 11 = 2048` different settings. It has half that.
So 10 is the most inputs it can memorise, and it is the same for every
design of network.

A third count, for the squeezing of places, follows. Send 6 birds through
the layers of a network that tells 2 colours apart. After each layer the
birds occupy some number of places. That number can never go up, it starts
at no more than 6, and it can never fall below 2. If it did, two colours
would share a place and one of them would be wrong.

## The statement

The first count is for models that are linear in their weights.

```lean
theorem finrank_le_of_fits_all
    (predict : Weights →ₗ[ℝ] Outputs)                              -- `→ₗ[ℝ]`: linear, so twice the weights give twice the outputs
    (fits_every_labels : ∀ labels, ∃ weights, predict weights = labels) :
    let label_count  := finrank ℝ Outputs                          -- one label for each data point: the number of data points
    let weight_count := finrank ℝ Weights                          -- `finrank`: how many numbers the weights hold
    label_count ≤ weight_count := by
```

*Read aloud:* if a model that is linear in its weights can fit every set
of labels, it has at least as many weights as data points.

`finrank` is the number of independent numbers a space holds: 19 weights
is a space with `finrank` 19. The theorem `exists_unfittable` is the same
fact turned round: with fewer weights than data points, some labels have no
fit.

The second count lets the weights be anything, but written in a fixed
number of bits.

```lean
theorem card_le_bits_of_memorises
    (network : YesNoNetwork Settings Inputs)
    (chosen_inputs : Finset Inputs)
    {bit_count : ℕ}
    (settings_fit_in_bits : Fintype.card Settings ≤ 2 ^ bit_count)  -- `bit_count` bits spell out at most `2 ^ bit_count` settings
    (memorises_every_labelling :
      ∀ labelling : YesNoLabelling chosen_inputs,
        ∃ setting, ∀ input : chosen_inputs,
          network setting input = labelling input) :
    let input_count := chosen_inputs.card
    input_count ≤ bit_count := by
```

*Read aloud:* if a network whose weights take `bit_count` bits realises
every yes-or-no labelling of some inputs, there are at most `bit_count`
of them.

`Fintype.card Settings` is how many settings of the weights exist.
`YesNoLabelling chosen_inputs` is one yes or no for each chosen input.

The third count is about places. In the repository a layer is a function
from places to places, and the theorem `bottleneck` says that for a flock
the network gets right, the count of places after any layer sits between
two walls.

```lean
    let places_after_early := flock.image (RUN_LAYERS early_layers)
    let label_count := (flock.image label).card
    let place_count := places_after_early.card
    let input_count := flock.card
    let at_least_labels := label_count ≤ place_count
    let at_most_inputs  := place_count ≤ input_count
    at_least_labels ∧ at_most_inputs := by
```

I left out the arguments above these lines. They are the layers, the
readout, the labels and the hypothesis `network_is_right`.

*Read aloud:* the number of labels is at most the number of places, which
is at most the number of inputs.

## Why it is true

**One weight for each label.** A linear map cannot reach more dimensions
than it starts from. If the predictions reach every set of labels, then
the labels' space is no bigger than the weights' space. That is the whole
proof.

**One bit for each answer.** Every labelling must be produced by some
setting, and one setting produces only one labelling. So there are at least
as many settings as labellings, `2 ^ input_count`. There are at most
`2 ^ bit_count` settings. Compare the powers of two.

**The walls.** If two inputs land on
the same place at some layer, they stay together for every layer after it
(`merged_stays_merged`, in an earlier file). So they get the same answer.
If the network is right on both, they have the same label
(`label_eq_of_merged`). That is the lower wall. The upper wall is that an
image of a finite set is no bigger than the set.

When a layer has squeezed all the way down to as many places as labels, two
inputs share a place exactly when they share a label (`merged_iff_label_eq`).

## What it explains

**Memorisation.** Networks that fit random labels (**recalled**: Zhang et
al. 2017) do so because they have the room. The first count gives the
threshold for a model that is linear in its weights, and it is where the
peak of double descent sits in chapter 10.

**Compression.** The note `code-length.md` reads three earlier results as
statements about writing things down briefly. A code of `digit_count`
digits names at most `2 ^ digit_count` things (`card_le_two_pow_of_code`).
A fold throws away one bit, and `fold_count` folds throw away at most
`fold_count` bits (`card_le_two_pow_of_iterate_tent_eq`). A layer is one
digit, and depth is code length. No model has average log-loss below the
entropy of the data (`gibbs`). And the travel of chapter 9, taken as a
description length, is shortest for gradient descent
(`descriptionLength_gradientDescent_le`) and falls as the model grows
(`travel_sq_div_eq_of_tight`). That the description length goes as
squared distance is a definition here, taken from (**recalled**: Hinton
and van Camp 1993).

**Gates and bottlenecks.** `Mixtures.lean` adds two more results.
Blending experts with a gate adds slope only through how far apart the
experts are (`abs_mixture_sub_le`). And the table of scores of a last
layer with `hidden_count` hidden numbers has rank at most that many
(`rank_scoreTable_le`), so it cannot be every table.

**The information bottleneck.** The view that a network discards what the
label does not need is (**recalled**: Tishby and Zaslavsky 2015). The
counting version above is the part that is proved. Whether training moves
a real network to the lower wall is disputed (**recalled**: Saxe et al.
2018).

## How this meets the squiggly line

A squiggly curve passes near every point, and it is tempting to read that
as "it can fit anything". The counts say otherwise. Nearness (chapter 4)
is about where the curve goes. Fitting chosen labels at chosen inputs is
about how many free numbers the curve has. The tent curve of chapter 8
comes within `1 / 2 ^ fold_count` of every point and has only a few
neurons to set. It has the folds of chapter 8 and the travel of chapter 9,
and neither of them is storage.

## What is not shown

- **Networks that are not linear in their weights, with exact real
  weights.** The first count is for models linear in their weights. The
  second needs weights of finite precision. For ReLU networks with real
  weights the known bounds are of another kind (**recalled**: Bartlett et
  al. 2019). **open** here.
- **Random labels are the worst case.** Capacity for labels with structure
  is a different and harder question. **open**
- **Counting is not Shannon information.** The count of places ignores how
  many birds sit at each place, and layers here are exact functions with no
  noise. **open**
- **That training compresses.** Nothing here says gradient descent moves a
  network to the lower wall. **open**
- **Huffman's method and Kraft's inequality itself.** Kraft's inequality is
  an assumption in `expected_length_ge_entropy`.

## Check yourself

1. A model linear in its weights has 50 weights. What is the most data
   points it can fit with every possible set of labels?
2. Weights written in 20 bits. What is the most inputs the network can be
   made to label in every possible yes-or-no way?
3. A flock has 12 inputs and 3 labels, and the network gets all of them
   right. How many places can the flock occupy after the third layer?

**Answers.** (1) At most 50, by `finrank_le_of_fits_all`. (2) At most 20,
by `card_le_bits_of_memorises`. (3) At least 3 and at most 12, by
`bottleneck`. The count could be anywhere in that range, and it can only
fall as the layers go on.

Previous: [33. Convolution](33-convolution.md) · Next: [35. The landscape: connected fits and collapsed classes](35-the-landscape.md)
