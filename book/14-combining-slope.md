# 14. Three ways to combine slope

**In the repository:** the files in
[`Supporting/NetworkShape/`](../lean/SquigglyLine/Supporting/NetworkShape),
with notes in
[`docs/supporting/network-shape/`](../docs/supporting/network-shape).
**You need:** chapters 3 and 7.

## The idea

Chapter 3 said nearness is bought with slope. So the question to ask of
any network design is: what does it do to slope? Across every result
about architecture in the repository there are only three answers.

> Stacking multiplies slope. Averaging never raises it. A skip adds one.

## Stacking multiplies it

A network is no steeper than the product of the slopes of its layers,
and the gradient comes back through the same product
([`NetworkSlope`](../lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean)).
Several known facts are this one fact.

- **Adversarial examples.** To flip a classifier whose slope is at most
  `slope_limit`, an input must move by at least
  `score / slope_limit`. A steep classifier can be fooled by a small
  nudge. This is chapter 3 read backwards.
- **Vanishing and exploding gradients.** If each layer has gain `gain`,
  then `depth` layers have gain `gain ^ depth`. It dies below one and
  blows up above
  ([`VanishingGradients`](../lean/SquigglyLine/Supporting/NetworkShape/VanishingGradients.lean)).
  A sigmoid's slope is never above one quarter, so sigmoid layers fade
  fast
  ([`Activations`](../lean/SquigglyLine/Supporting/NetworkShape/Activations.lean)).
- **Initialisation.** A fold keeps exactly half the mean squared size of
  a signal that is as often negative as positive. The factor two in He
  initialisation puts it back
  ([`Gain`](../lean/SquigglyLine/Supporting/NetworkShape/Gain.lean)).
- **Convolution.** A convolution layer is no steeper than the summed
  sizes of its kernel weights. Reading every second position is a
  squeeze by two, so by chapter 7 it doubles the slope
  ([`Convolution`](../lean/SquigglyLine/Supporting/NetworkShape/Convolution.lean)).
- **Temperature.** Dividing the scores by a temperature divides their
  slope and never changes their order.

## Averaging never raises it

An average of models is no steeper than the steepest of them
([`Averaging`](../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean)).
The same holds for the higher of two lines, which covers max-pooling,
and for a model averaged over shifted or turned copies of its input,
which covers augmentation. Chapter 15 is about what averages can and
cannot do.

## A skip adds one

A residual layer outputs its input plus a branch. If the branch has
slope at most `branch_slope`, the layer has slope between
`1 − branch_slope` and `1 + branch_slope`
([`Residual`](../lean/SquigglyLine/Supporting/NetworkShape/Residual.lean)).
That one line says a lot.

- With `branch_slope` below one, the lower bound is above zero. So the
  layer never merges two inputs, which answers question 3 of chapter 12.
- A stack of `depth` such layers, each with a branch of slope
  `budget / depth`, has total slope at most `e ^ budget`, however deep
  it is. Depth without explosion.
- The memory cell of an LSTM is the same thing. Its slope per step is
  the forget gate, and exactly one with the gate open.

In the optics picture of chapter 12, a skip is a beam that goes round
the plate and rejoins, and a normalisation is an amplifier after it
([`SkipAndNorm`](../lean/SquigglyLine/Supporting/NetworkShape/SkipAndNorm.lean)).
Both hold the factor of chapter 13 at one.

## Gates, the one way round the rules

A gate blends several experts using weights that depend on the input.
Its output changes by at most what the experts change, **plus** the
spread between the experts times how fast the gate changes
([`Mixtures`](../lean/SquigglyLine/Supporting/NetworkShape/Mixtures.lean)).
So a blend of gentle experts can still be steep where the gate switches
quickly between experts that disagree. Attention is such a gate.

## What follows

Squiggle can only come from stacking pieces that are steep or that fold
(chapter 8). No amount of averaging makes it, and skips only carry it.

## What is not shown

These are upper limits on slope. A real network is usually far gentler
than the product of its layers allows, and how much gentler is not
proved here.

## Check yourself

1. A network has five layers, each with slope at most 2. How steep can
   it be?
2. A classifier has slope at most 10, and gives a score of 0.5 to its
   answer. What is the smallest move of the input that could flip it?
3. A hundred residual layers each have a branch of slope 0.01. How steep
   can the stack be? What if the same branches were stacked without
   skips?

**Answers.** (1) At most 32. (2) At least 0.05. (3) At most `e`, about
2.72. Without skips the slope is at most `0.01 ^ 100`: the signal is
gone.

Previous: [13. One factor, again and again](13-one-factor.md) · Next: [15. Averages](15-averages.md)
