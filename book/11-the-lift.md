# 11. The lift

**In the repository:**
[`Lift.lean`](../lean/SquigglyLine/Networks/Lift.lean),
[`FourierLift.lean`](../lean/SquigglyLine/Networks/FourierLift.lean),
[`RadialBasis.lean`](../lean/SquigglyLine/Networks/RadialBasis.lean),
[`RandomFourier.lean`](../lean/SquigglyLine/Networks/RandomFourier.lean),
[`Positions.lean`](../lean/SquigglyLine/Networks/Positions.lean),
note [`kernel-trick.md`](../docs/networks/kernel-trick.md).
**You need:** chapters 3, 7 and 10.

## The idea

Part I was about how squiggly the line is. Chapters 9 and 10 were about
how far the weights move. This chapter is the bridge between the two.

A model that is linear in its weights works in two steps. First it
**lifts** the input to a list of features, usually a much longer list
than the input. Then it takes the dot product of that list with the
weights.

Upstairs, in the space of features, the model is a flat plane. Downstairs,
seen as a function of the input, it is a squiggly line.

> Squiggly below, flat above.

| Name | Meaning |
|---|---|
| `FeatureMap` | the lift: an input to its list of features |
| `EVALUATE_LIFTED_MODEL` | the model: lift, then dot with the weights |
| `GET_LIFT_KERNEL` | the overlap of two inputs upstairs |

## Four facts about any lift

1. **A point is on the squiggly line exactly when its lift is on the
   plane** (`embed_mem_curve_liftedModel_iff`).
2. **The slope downstairs is at most the size of the weights times the
   stretch of the lift** (`lipschitzWith_liftedModel`). The stretch is how
   much the lift can pull two nearby inputs apart. So chapter 3's price
   of nearness can be paid in two ways: big weights, or a lift that
   stretches.
3. **The kernel trick** (`liftedModel_add_sum`). If the weights have
   moved from their start only along the lifted data points, then the
   prediction at a new input is the starting prediction plus a sum over
   the data: a number for each data point, times the kernel between that
   point and the new input. The features themselves never have to be
   written down. Gradient descent only ever moves the weights that way.
4. **A warning** (`exists_lift_eq`). Any function at all is flat in some
   lift. So "it is flat upstairs" says something only when the lift is
   fixed before the data is seen.

## The Fourier lift

Wind the input round a circle:

```
lift(input) = (cos(frequency × input), sin(frequency × input))
```

A flat plane over that circle is, downstairs, a wave:
`cosine_weight × cos(...) + sine_weight × sin(...)`. This is the sine of
chapter 6, seen as a lifted model.

- The kernel of two inputs is `cos(frequency × gap)`, where `gap` is
  how far apart they are (`liftKernel_fourierLift`). It sees only the
  gap. So shifting the data and the question together changes no answer.
- The lift stretches distances by at most `frequency`
  (`lipschitzWith_fourierLift`). So by fact 2 the wave is no steeper than
  the size of its weights times its frequency. The frequency is the
  squeeze factor of chapter 7, now appearing as the stretch of a lift.

## Bumps

A radial basis network is a sum of bell-shaped bumps, one centred at each
of some chosen places, all of one width.

A bump of width `width` is the unit bump squeezed sideways by
`1 / width` (`bump_eq_compress`). So chapter 7 applies with `1 / width`
as the squeeze factor. Narrow bumps are steep, with slope up to
`1 / width`, and reach every label: once the bumps hardly overlap, they
fit any labels exactly (`exists_heights_of_gap`). Wide bumps are gentle
and cannot.

## The wave and the bump are one thing

Use many frequencies at once, drawn from a bell curve with variance
`variance`. The Fourier kernel, averaged over that draw, is

```
exp(−variance × gap² / 2)
```

which is the bump (`integral_liftKernel_fourierLift`). So a wide layer of
random waves and a radial basis network have the same kernel on
average, and by chapter 10 they are then the same learner. This is the
idea behind random Fourier features.

## Telling a transformer where a token is

The same reasoning covers position embeddings
([`Positions.lean`](../lean/SquigglyLine/Networks/Positions.lean)). The
overlap of the sinusoidal signals of two positions is a sum of cosines of
the gap between them, so it depends only on the gap. Rotary positions
turn the query and the key so that the score depends on the positions
only through the gap, and no vector changes length. A learned table ties
no two positions together.

## What is not shown

A lift that is **learned**. In a deep network the earlier layers are the
lift, and training changes them. Everything here holds for the lift as
it stands at one moment.

## Check yourself

1. A Fourier lift has frequency 10. Two inputs are 0.01 apart. At most
   how far apart are their lifts?
2. Its weights have size 3. What is the most its slope can be?
3. Bumps of width 0.1 against bumps of width 1: which can fit labels
   that change quickly, and what do they pay?

**Answers.** (1) 0.1. (2) 30. (3) The narrow ones can. They pay in
slope: up to ten times steeper for the same heights.

Previous: [10. The kernel](10-the-kernel.md) · Next: [12. Layers as polarizers](12-polarizers.md)
