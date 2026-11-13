# The bridge between the Fourier model and the ReLU wind tunnel

Notes from 11 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in `lean/`), **checked** (by a
calculation here), or **recalled** (from the literature).

## The short answer

The two models are not the same thing, so "equivalent" has to be said
carefully. There are three bridges. Two are exact. The third is where they
differ, and it is the one that matters for training.

| Bridge | What it says | Status |
|---|---|---|
| Same dial | One fold of the wind tunnel doubles a frequency. Depth is the logarithm of frequency. | exact |
| Same skeleton | Both are "features times weights". For training, a model is its kernel and nothing else. | exact |
| Different geometry | They can draw the same curves, but at very different exchange rates. | measured |

## Bridge 1: a fold is a frequency doubling

Take the two-neuron layer `APPLY_TENT` from `Depth.lean`. It folds the interval
`[0, 1]` in half. Now look at its output through one fixed lens, the function
`sin²(π/2 · y)`. Then

```
sin²(π/2 · tent(x)) = sin²(π · x)
```

The layer has doubled the angle inside the sine. Stack `L` layers:

```
sin²(π/2 · tent^L(x)) = sin²(2^(L−1) · π · x)
```

(**proved**: `sin_sq_iterate_tent` in `Bridge.lean`; also **checked** to machine
precision for `L` up to 10.)

The right side is a single Fourier term: `sin²(a) = (1 − cos(2a)) / 2`, so it
is one cosine of frequency `2^L`. So:

> A wind tunnel of `L` folds, seen through a fixed smooth lens, is exactly one
> Fourier term of frequency `2^L`.

This gives the dictionary between the two models.

| Fourier model | ReLU wind tunnel |
|---|---|
| frequency of a term | `2^depth` |
| number of terms | number of neurons across a layer |
| a sine wave | a triangle wave (the same wave drawn with straight pieces) |
| raising the frequency | adding a fold |

It also joins the polarizer picture. Doubling an angle is a rotation. A fold
of the wind tunnel is a rotation of the phase by its own size. The one-neuron
tunnel cannot fold, so it cannot double anything, so it never turns.

One caution. In the Fourier model a high frequency costs one parameter. In the
wind tunnel it costs depth, and only the logarithm of the frequency. So the
wind tunnel reaches high frequencies much more cheaply. That is the
`width^depth` resolving power again.

## Bridge 2: for training, a model is its kernel

Both models have the same skeleton when only the last layer is trained:

```
output = weight₁ · feature₁(x) + weight₂ · feature₂(x) + …
```

For the Fourier model the features are sines and cosines. For a ReLU network
with its earlier layers held fixed, the features are whatever the last hidden
layer computes: hinges, or folded shapes.

Everything proved for the Fourier model used only this skeleton. So it holds
for the ReLU model too, word for word: the loss curve along the straight path,
"loss gap equals distance times steepness", and "more parameters never move
the fit away" (**proved**: `LinearModel.lean`).

More is true. Write `A` for the map from weights to outputs on the data. The
kernel is `K = A·Aᵀ`: it records how alike the features make two data points
look. Then:

- A gradient step changes the error by `error ← error − η · K · error`. The
  weights do not appear (**proved**: `residual_gradientStep` in `Kernel.lean`).
- The travel to the nearest fit is `√(errorᵀ · K⁻¹ · error)`. The weights do
  not appear (**proved**: `travel_eq_norm_of_kernelInverse`).

So two models with the same kernel on the data are the same learner. They have
the same travel, and gradient descent takes them through the same sequence of
outputs (**proved**: `travel_eq_of_kernel_eq`, `residual_iterate_gradientStep_eq`). That is the exact sense in which a Fourier model and a ReLU model can
be equivalent: when their kernels agree.

## Where they differ: the exchange rate

They can draw the same curves on the data. With at least as many independent
features as data points, either model can produce any set of outputs. So one
is a change of basis of the other.

But the change of basis is not a rotation. It stretches some directions and
squeezes others, so distances in parameter space do not match.

- **Fourier features are nearly orthogonal.** Every direction in data space is
  about equally cheap to reach. With 513 parameters and 20 points, the largest
  and smallest stretch differ by a factor of 1.7 (**checked**).
- **Hinge features overlap heavily.** Every hinge is switched on over a large
  part of the input, so the features look alike. Some directions are very
  cheap and some are very expensive. For 513 random hinges on the same 20
  points the factor is about 300,000,000 (**checked**).

So the two models are equal in what they can draw and far apart in how hard it
is to get there. For a raw ReLU model the exchange rate depends strongly on
direction. Smooth targets are cheap. Sharp, wiggly ones are expensive. This is
the known "spectral bias" of ReLU networks (**recalled**).

There is a second difference. The Fourier model is exactly linear in its
parameters. A ReLU network is linear only in its last layer. Moving an earlier
weight moves a kink, which is not a linear change. The skeleton above holds
exactly for last-layer training, and approximately for a very wide network
(**recalled**: the lazy-training results).

## What was to prove (all three now proved)

1. **The fold identity.** `sin²(π/2 · tent^L(x)) = sin²(2^(L−1) · π · x)` on
   `[0, 1]`.
2. **Gradient descent sees only the kernel.** One step maps the error to
   `error − η · K · error`.
3. **Travel sees only the kernel.** If `K` is invertible, the travel is
   determined by `K` and the error. Two models with the same kernel have the
   same travel.

Together: same kernel means same learner, and one fold means one doubling of
frequency.

## What cannot be proved, because it is false

- That the two models are equivalent with no condition. They are equivalent
  as learners exactly when their kernels agree, and for raw hinges against
  Fourier features the kernels are very different.
- That a full ReLU network, with every layer trained, is a linear model.
