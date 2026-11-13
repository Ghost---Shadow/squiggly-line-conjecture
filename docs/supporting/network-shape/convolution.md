# Convolution, stride and upsampling

**Proofs:** [`Compression.lean`](../../../lean/SquigglyLine/Theorem/Compression.lean), [`Convolution.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/Convolution.lean).

Notes from 14 Nov 2026. Each statement is marked **proved**, **argued**,
**recalled** or **open**.

## The idea

A convolution layer slides one small kernel along a signal. `fourier-lift.md`
shows what that is built to give: the same line when the data is shifted.
This note is about the layer itself: how much slope it can add, how far it
can see, and what stride and upsampling do to squiggle. The signal here has
one dimension.

## The layer

Proofs in
[`lean/SquigglyLine/Supporting/NetworkShape/Convolution.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/Convolution.lean). 
- **Slope.** If two signals differ by at most `d` at every position, their
  outputs under one convolution layer differ by at most `d` times the
  summed sizes of the kernel weights (**proved**:
  `abs_convolution_sub_le`). The length of the signal does not enter. So
  the slope a convolution layer can add is set by its few kernel weights.
- **Locality.** An output depends only on the inputs under the kernel
  (**proved**: `convolution_congr`). After `L` layers with a kernel of
  width `n`, it depends only on the inputs within `L * n` of it
  (**proved**: `iterate_convolution_congr`). Squiggles are made locally,
  and the same kernel makes them at every position.
- **Stride.** Reading a signal at every second position is squeezing it
  sideways by two, in the exact sense of the general theorem (**proved**:
  `stride_eq_compress`). So each stride doubles the slope of what the later
  layers see (**proved**: `lipschitzWith_stride`), and with it the
  frequency.
- **Upsampling.** Stretching by two is squeezing by one half (**proved**:
  `upsample_eq_compress`). A stride of two after it gives the signal back
  (**proved**: `stride_upsample`). This is the way down and back up in a
  U-shaped network.

## How this meets the squiggly line

Through **slope** and through the general theorem. A convolution layer's
slope is set by a few kernel weights, and it makes squiggle locally. A
stride is a squeeze in the exact sense of [`Compression.lean`](../../../lean/SquigglyLine/Theorem/Compression.lean): closer,
steeper by the same factor, and no better in loss.

## What is not shown

- **Images.** The kernel here has one dimension.
- **Pooling as the way to downsample.** Max pooling of two lines is in
  `vanishing-gradients.md`.
- **Padding and the edges of the signal.** The signal here goes on for ever
  in one direction.
