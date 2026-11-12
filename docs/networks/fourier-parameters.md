# What adding parameters changes, in plain words

Notes from 11 Nov 2026. This is the Fourier-series version of the conjecture:
the one family here where the number of parameters is the only dial.

Each statement is marked **proved** (in `lean/`), **checked** (by
`scripts/fourier_params.py` or a calculation), or **recalled** (from the
literature, not verified in this repository).

## Why sines alone were not enough

The first experiments used one sine, `A·sin(w·x + φ)`. It has three numbers:
amplitude, frequency and phase. Only the phase was random. Frequency was a
dial for squiggliness, not a count of parameters. So those experiments could
say "squigglier is closer" and could not say anything about "more parameters".

A single sine also cannot fit more than two points at once, at any frequency.

## The family

A Fourier series with `m` terms:

```
f(x) = a₀ + a₁·cos(πx) + b₁·sin(πx) + … + a_m·cos(mπx) + b_m·sin(mπx)
```

It has `2m + 1` parameters, the coefficients. A random model draws each
coefficient at random. The coefficients are scaled down as `m` grows, so that
the output has the same spread at every `m`. This matters: without it, a
bigger model is simply louder, and everything below would measure loudness.

The data is 20 points with random labels. A model can fit all 20 points once
it has 20 parameters. That is the threshold.

## This is a generalized linear model

A generalized linear model has three parts (**recalled**: the standard
definition).

- **A weighted sum of fixed features.** The features do not change in
  training. Only the weights do.
- **A link.** A fixed function that turns the sum into a prediction.
- **A noise model.** It decides which loss is used.

The Fourier series is the plainest case. The features are the sines and
cosines. The weights are the coefficients. The link does nothing, and the loss
is squared error. That is linear regression in sine and cosine features.

The single sine of the first experiments is not one. Its frequency and phase
sit inside the sine, so the output is not a weighted sum of fixed features.

The results below divide by which part they use.

- **The weighted sum only.** Travel, the exchange rate, the double-descent
  peak in travel, and "more parameters never move the fit away" are
  statements about the features and a target. Under another link the target
  is the labels read on the link's scale, and the statements stay the same
  (**argued**, not proved here). They need that target to be finite. For a
  yes-or-no label under the logistic link it is not, so no exact fit exists
  at any distance.
- **No link and squared error.** "The error left is `1 − t` times the
  starting error", the gradient-descent step, and everything proved about its
  speed and stability use both.
- **Neither.** That the initial loss does not move (`Marginal.lean`) holds for
  any model and any loss of this kind.

## Four things to measure

- **Initial loss.** The usual training loss of the random model, before any
  training. It measures vertical error.
- **Nearest-point distance.** How close the random curve passes to each data
  point in any direction. This is the distance of the original conjecture.
- **Travel.** The distance in parameter space from the random start to the
  nearest set of coefficients that fits every point.
- **Steps.** How many gradient-descent steps it takes to fit, at the largest
  stable step size.

## What happens as parameters are added

| parameters | initial loss | nearest-point distance | travel | steps |
|---|---|---|---|---|
| 9 | 0.65 | 0.229 | no fit exists | never |
| 21 | 0.65 | 0.128 | 448 | 188,000,000 |
| 25 | 0.64 | 0.110 | 35.5 | 79,300 |
| 65 | 0.71 | 0.056 | 1.61 | 166 |
| 129 | 0.66 | 0.027 | 0.48 | 13 |
| 513 | 0.63 | – | 0.23 | 3 |

(**checked**)

- **The initial loss does not move.** It is about 2/3 at every size. The
  differences are sampling noise. This has to be so: the loss depends only on
  how the output is distributed at each single input, and the scaling keeps
  that the same (**proved**: `Marginal.lean`).
- **The nearest-point distance falls**, roughly like one over the parameter
  count. Random series with more terms are steeper, and steep curves pass
  close to everything.
- **Travel falls steeply**, and so do the steps. From 21 to 513 parameters the
  travel drops about 2,000 times, and training goes from 188 million steps
  to 3.
- **The worst place is the threshold.** With 21 parameters for 20 points a fit
  exists but is very far away. This is the peak of double descent.

## A bigger model is not nearly right. It is nearly adjustable.

"Already almost trained" can mean two things.

- **Low loss at the start.** False. A big random model is as wrong as a small
  one.
- **Few parameter changes away from a solution.** True. This is what makes
  training fast.

With more parameters, a small nudge to each one adds up to a large change in
the output. So a solution sits close to wherever the model starts. This is the
known lazy-training picture (**recalled**: Jacot et al. 2018, Du et al. 2019,
Chizat and Bach 2019). It is not a new result.

## Loss and travel are one quantity at an exchange rate

Slide the parameters in a straight line from the random start to the nearest
fit. At fraction `t` of the way, the error left is `1 − t` times the starting
error. This is the same at every model size (**proved**:
`residual_along` in `LinearModel.lean`).

So every model walks the same loss curve. What differs is how long the walk
is. Loss gap equals distance times steepness: a model whose fit is at distance
`d` removes the fraction `ε / d` of its error by moving a distance `ε`
(**proved**: `exists_within_budget`).

This gives the form in which the original idea is true:

> At a movement budget of zero, a bigger random model is no closer to the
> data. At any positive budget, it is closer.

Adding parameters never moves the nearest fit further away (**proved**:
`travel_coprod_le`, for new parameters that start at zero).

## The exchange rate

If the features are orthogonal on the data side, each with squared length `c`,
then

```
travel = (size of the error) / √c
```

exactly (**proved**: `TightFeatures.travel_eq` in `ExchangeRate.lean`).

With as many orthonormal features as data points, `c = 1`. Then parameter
space is data space and travel equals the error (**proved**:
`travel_eq_norm_residual`).

Random Fourier features on scattered points are nearly orthogonal when there
are many more terms than points, with `c = m + 1`. That predicts

```
travel ≈ √(n × initial loss / (m + 1))
```

which gives 0.45, 0.32 and 0.22 for 129, 257 and 513 parameters, against 0.48,
0.34 and 0.23 measured (**checked**). So far above the threshold, travel falls
like one over the root of the parameter count. Near the threshold the features
are far from orthogonal and the formula fails badly: it predicts 0.88 at 33
parameters and the measurement is 16.

## What is still open

- That random Fourier features are nearly orthogonal is checked, not proved.
- The proved statement about adding parameters starts the new ones at zero.
  The experiment starts them at random.
- Everything here is for models that are linear in their parameters. A neural
  network is only approximately so, and only when it is very wide.
- Everything proved about training is for squared error with no link. What
  carries over to other links, such as the logistic one, is listed in
  `docs/open-problems.md`, items 25 to 28.
