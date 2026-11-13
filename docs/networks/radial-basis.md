# Radial basis functions: the width of a bump is its slope

**Proofs:** [`Compression.lean`](../../lean/SquigglyLine/Theorem/Compression.lean), [`Kernel.lean`](../../lean/SquigglyLine/Networks/Kernel.lean), [`Lift.lean`](../../lean/SquigglyLine/Networks/Lift.lean), [`RadialBasis.lean`](../../lean/SquigglyLine/Networks/RadialBasis.lean), [`RandomFourier.lean`](../../lean/SquigglyLine/Networks/RandomFourier.lean).

Notes from 13 Nov 2026. Written before the proofs, then updated once they
were done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Networks/RadialBasis.lean`](../../lean/SquigglyLine/Networks/RadialBasis.lean)), **argued**, **recalled** or
**open**.

## The idea

A radial basis network is a sum of bumps. Each bump sits at a centre, has a
height, and falls off with the distance from its centre. All the bumps share
one width.

    network(input) = sum of height[i] * bump((input - centre[i]) / width)

The bump used here is the Gaussian one, `exp(-t² / 2)`.

The claim on the wishlist was: a narrow bump is a steep one, so the width of
the bump sets how squiggly the line can be. That turns out to be the theorem
of this project with the width in the place of the frequency.

## A bump of width `width` is the unit bump, squeezed

Dividing the input by the width before applying the unit bump is squeezing
the unit bump sideways by `1 / width` (**proved**: `bump_eq_compress`).

So everything [`Compression.lean`](../../lean/SquigglyLine/Theorem/Compression.lean) says about a squeezed function holds for a
bump. In particular its slope is the slope of the unit bump times
`1 / width`.

The unit bump never climbs faster than one (**proved**:
`lipschitzWith_unitBump`). The exact figure is `1 / √e`, about 0.61; the
proof here settles for one. So a bump of width `width` has slope at most
`1 / width` (**proved**: `lipschitzWith_bump`).

## The network is no steeper than its heights over its width

A sum of bumps has slope at most the sum of the sizes of the heights,
divided by the width (**proved**: `lipschitzWith_bumpNetwork`).

Put that into the slope sandwich. The vertical error is at most
`√(1 + slope²)` times the nearest distance (**proved**:
`verticalDist_bumpNetwork_le`). So a network of wide bumps and modest
heights cannot pass near a data point it misses by a lot. To be near, it
must have narrow bumps or large heights. Those are the two dials of a radial
basis network, and both are slope.

## It is a lift, so the kernel results apply

The list of bump values at an input is a lift of the input, and the network
is a flat model on that lift (**proved**: `bumpNetwork_eq_liftedModel`). So
the results of [`Lift.lean`](../../lean/SquigglyLine/Networks/Lift.lean) hold for it: it trains through its kernel, and the
kernel of two inputs is the overlap of their bump lists.

The bump itself depends only on the distance between input and centre, so
shifting both by the same amount changes nothing (**proved**:
`bump_shift`). A network with a bump at every data point gives the same line
when the data is shifted.

## Narrow bumps fit anything

Put one bump on each data point. If the bumps hardly overlap, the network
can be given heights that fit any labels exactly (**proved**:
`exists_heights_of_small_overlap`). "Hardly overlap" means: at each data
point, the other bumps together are worth less than the point's own bump,
which is one.

That is the case once the bumps are narrow against the gaps in the data. If
every two inputs are at least `gap` apart, each of the other bumps is worth
at most `exp(-(gap / width)² / 2)` (**proved**: `bump_le_of_gap`), and that
goes to zero as the width shrinks. With `n` data points the bumps are narrow
enough once `(n - 1) * exp(-(gap / width)² / 2)` is below one (**proved**:
`exists_heights_of_gap`).

So a radial basis network memorises by narrowing, and the section above
says what that costs: slope `1 / width`.

## The Fourier lift, averaged, is the bump

Notes from 14 Nov 2026. Proofs in
[`lean/SquigglyLine/Networks/RandomFourier.lean`](../../lean/SquigglyLine/Networks/RandomFourier.lean).

The kernel of the Fourier lift of frequency `w` is `cos(w * gap)`, where
`gap` is the difference of the two inputs (`fourier-lift.md`). Draw the
frequency from a bell curve of mean zero and variance `v`. The mean of
`cos(w * gap)` is then `exp(-v * gap² / 2)` (**proved**:
`integral_cos_gaussian`). That is the Gaussian bump of the gap, with width
`1 / √v`.

So the kernel of the Fourier lift, averaged over random frequencies, is the
radial basis kernel (**proved**: `integral_liftKernel_fourierLift`). A wide
layer of random cosine features and a network of bumps train as the same
model, on average. A wide spread of frequencies is a narrow bump: the two
dials of squiggliness, frequency and one over width, are the same dial.

Not shown: how many random features are needed for the average to be close
(**recalled**: Rahimi and Recht 2007).

## How this meets the squiggly line

The theorem says a squigglier line is closer to the data and steeper by the
same factor. For sines the dial was the frequency. For a radial basis
network the dial is `1 / width`. A bump is a squeezed unit bump, in the
exact sense of [`Compression.lean`](../../lean/SquigglyLine/Theorem/Compression.lean).

Narrow bumps reach every label and are steep. Wide bumps are gentle and
cannot reach. Nothing else is traded.

## What is not shown

- **The exact slope.** The unit bump's steepest slope is `1 / √e`. Only the
  bound one is proved.
- **Many input dimensions.** The file is for real inputs, as the theorem for
  sines is.
- **The kernel as a lift in its own right.** The Gaussian kernel is the
  overlap of two lifts into a space of infinitely many dimensions
  (**recalled**). Here only a network with finitely many centres is written
  as a lift.
- **What training does.** Which heights gradient descent finds is the kernel
  story of [`Kernel.lean`](../../lean/SquigglyLine/Networks/Kernel.lean), not repeated here.
