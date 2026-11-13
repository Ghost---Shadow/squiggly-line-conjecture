# The Fourier lift: Fourier features, position signals and convolution

**Proofs:** [`FourierLift.lean`](../../lean/SquigglyLine/Networks/FourierLift.lean), [`Positions.lean`](../../lean/SquigglyLine/Networks/Positions.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Networks/FourierLift.lean`](../../lean/SquigglyLine/Networks/FourierLift.lean) unless another file is named),
**argued**, **recalled**, or **open**.

## The idea

`docs/networks/kernel-trick.md` says a squiggly line is a flat plane seen
through a lift, and that its slope is at most

```
tilt of the plane × stretch of the lift
```

This note works that out for the lift the repository started with, and finds
three well-known methods inside it.

## The lift

Wind the input round a circle: `x ↦ (cos(w·x), sin(w·x))`. The number `w` is
the frequency. A flat plane over the circle, with weights `(a, b)`, is the
wave `a·cos(w·x) + b·sin(w·x)` downstairs (**proved**:
`liftedModel_fourierLift`).

Two inputs a distance `d` apart land `√(2 − 2·cos(w·d))` apart on the circle
(**proved**: `norm_fourierLift_sub_sq`). For small `d` that is about `w·d`,
and it is never more:

> The Fourier lift stretches distances by at most its frequency.

(**proved**: `lipschitzWith_fourierLift`.) So the wave is no steeper than the
size of its weights times its frequency (**proved**:
`lipschitzWith_liftedModel_fourierLift`).

## Fourier features and NeRF

A plain network fed raw coordinates draws blurry pictures. Fed sines and
cosines of the coordinates at many frequencies, it draws sharp ones
(**recalled**: Tancik et al. 2020; Mildenhall et al. 2020).

In the terms of this repository the reason is one line. Nearness is bought
with slope. Slope is tilt times stretch. The network's own weights supply
only so much tilt in the time it trains. The Fourier lift supplies stretch
for free, in proportion to its top frequency. Raising the top frequency
raises the slope the model can reach, and with it how near the line can get
to fine detail. (**argued** from the proved bound)

The same bound gives the known cost. A lift with a very high frequency makes
a line that is squiggly everywhere, including between the data points
(**recalled**: the same papers report noise when the frequencies are set too
high).

## Position signals

A transformer is told where each token sits by adding sines and cosines of
its position, at several frequencies (**recalled**: Vaswani et al. 2017).
That is the Fourier lift applied to position.

The kernel of the lift is `cos(w·(x − x′))` (**proved**:
`liftKernel_fourierLift`). It depends only on how far apart the two positions
are, not on where they are (**proved**: `liftKernel_fourierLift_shift`). So
an attention head that scores by this kernel attends by relative position.
Moving along the sequence by `d` turns every lifted point through the same
angle `w·d` (**recalled**: the angle-addition formulas), which is what
rotary position signals use directly (**recalled**: Su et al. 2021).

## Convolution

A kernel that depends only on the gap between two inputs gives a learner
that does not care where things are. Shift every training input and the
question by the same amount, and the answer is the same (**proved**:
`liftedModel_shift`, for any lift with such a kernel).

A convolution layer builds this in by using the same weights at every place
(**recalled**: LeCun et al. 1989). In the terms used here it is a choice of
lift whose kernel sees only gaps.

## Four position embeddings

Notes from 14 Nov 2026. Proofs in
[`lean/SquigglyLine/Networks/Positions.lean`](../../lean/SquigglyLine/Networks/Positions.lean).

- **Sinusoidal, all frequencies together.** Give each position one cosine
  and one sine for every frequency. The overlap of the signals of two
  positions is a sum of cosines of the gap between them (**proved**:
  `positionOverlap_eq_sum_cos`). So it depends only on the gap (**proved**:
  `positionOverlap_shift`), and no two positions overlap more than a
  position does with itself (**proved**: `positionOverlap_le_card`,
  `positionOverlap_self`). This is the lift of the section above, with many
  frequencies at once.
- **Rotary.** Do not add a signal. Turn the query and the key, each by an
  angle set by its position. The dot product of the two is that of the query
  turned by the difference of the angles, with the key left alone
  (**proved**: `planeDot_rotate_rotate`). So the score depends on the two
  positions only through their gap (**proved**: `planeDot_rotate_shift`),
  and no vector changes length (**proved**: `planeDot_rotate_self`). The
  proof is for one pair of coordinates; a real model turns every pair, each
  at its own frequency.
- **Relative position bias.** Add to each score a number looked up by the
  gap. Shifting the whole sequence changes no gap, so it changes no bias
  (**proved**: `relativeBias_shift`).
- **Learned table.** Give each position a free vector. Changing the vector
  of one position changes nothing at any other (**proved**:
  `update_table_of_ne`). The table is a lookup, a lift that can fit
  anything, and it says nothing about a position it has not seen.

The first three build in the fact that only the gap matters. The table has
to learn it from data, and cannot use it past the longest sequence it was
trained on (**argued**).

## How this meets the squiggly line

This is the model of the first experiments and of section 5 of the README.
The frequency was the dial for squiggliness there. Here it has a precise
meaning: it is the stretch of the lift, and so the limit on slope per unit
of weight.

## What is not shown

- **Many frequencies at once.** The lift here has one. With several, the
  stretch is at most the root of the sum of the squared frequencies
  (**argued**).
- **That the bound is reached.** The stretch equals `|w|` in the limit of
  near inputs. Only "at most" is proved.
- **Why sharp pictures need the lift** is argued from the bound. No
  statement about training time is proved.
- **A convolution layer itself** is not modelled, only the property it is
  built to have.
