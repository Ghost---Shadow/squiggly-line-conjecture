# Averages: ensembles, weight averaging and the ideal denoiser

**Proofs:** [`ModeConnectivity.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/ModeConnectivity.lean), [`Averaging.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean), [`CrossEntropy.lean`](../../../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/NewInputs/Averaging.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean) unless another file is named),
**argued**, **recalled**, or **open**.

## The idea

The theorem says a line gets near the data by being steep. An average of
lines is never steeper than the steepest of them. So averaging is the one
common operation in deep learning that cannot add squiggle. Three well-known
methods are averages, and this is what each one buys.

## Ensembles

Train several models and average their answers.

The squared error of the average is the average squared error of the
members, minus how far the members are spread round the average:

```
error of the average  =  average error  −  spread
```

(**proved**: `sq_blend_sub`; **recalled**: Krogh and Vedelsby 1995.) The
spread is never negative, so the ensemble is at least as good as its members
are on average (**proved**: `sq_blend_sub_le`). It is strictly better
whenever the members disagree.

The average is also no steeper than its steepest member (**proved**:
`lipschitzWith_blend`).

Put the two together. Each member fits the data by being squiggly in its own
way. Between the data points the squiggles disagree, and the average cancels
them. The ensemble keeps the nearness of its members at the data and gives
back some of the slope they paid for it (**argued**). The spread is the
variance term of `docs/supporting/new-inputs/bias-variance.md`.

## Weight averaging

Averaging the answers of ten models costs ten times the compute at test
time. Averaging their weights gives one model. This is done along one
training run, or across several fine-tuned copies (**recalled**: Izmailov et
al. 2018; Wortsman et al. 2022, "model soups").

For a model that is linear in its weights the two are the same thing.
Averaging the weights is averaging the lines (**proved**:
`liftedModel_sum_smul`). So the averaged weights are at least as good as the
members are on average (**proved**: `sq_liftedModel_soup_sub_le`).

For a real network they are not the same. With just two weights multiplied,
the midpoint between a fit and its mirror image outputs zero
(`twoLayer_midpoint_mirror` in [`ModeConnectivity.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/ModeConnectivity.lean)). Weight averaging
works for networks only when the copies are close enough for the network to
behave like a linear model between them, which is the case when they share a
starting point (**argued**; **recalled**: Neyshabur et al. 2020).

## The ideal denoiser

A diffusion model is trained to remove noise. Given a noisy input, it should
return the clean example the noise was added to. It cannot know which one, so
the best it can do under squared error is the average of the candidates,
each weighted by how likely it is.

- Whatever the weights are, the weighted mean is the best single guess
  (**proved**: `sum_mul_norm_sub_sq`, `weightedMean_isBest`).
- With Gaussian noise of size `σ`, the weight of a training example falls
  with its squared distance from the noisy input: it is the softmax of
  `−distance² / 2σ²` (**recalled**: Bayes' rule; not proved here).
- So the ideal denoiser is an attention head. The query is the noisy input,
  the tokens are the training examples, and the score is nearness
  (**proved**: `idealDenoiser_eq_weightedMean`, `idealDenoiser_isBest`).
- Its output never leaves the region the training examples span (**proved**:
  `idealDenoiser_mem_convexHull`).

With a lot of noise every example gets about the same share and the output
is the plain average of the training set. With very little noise the nearest
example takes the whole share and the output is that example (**argued**).

## How this meets the squiggly line

The ideal denoiser's shares are set by the distance field of the training
set (`docs/supporting/network-shape/signed-distance.md`). It pulls a noisy
point toward the data by an amount that depends on how near the data is.

It also shows a puzzle clearly. A denoiser that reached its training target
exactly would only ever return blends of its training examples, and at low
noise it would return copies. Real diffusion models make new images. So they
do not reach the target. The network is too smooth to draw the ideal
denoiser, which at low noise is very steep near every training example. What
it draws in its place is the open question (`docs/wishlist.md`).

## What is not shown

- **The shares.** That the Bayes weights are the softmax above is recalled.
- **The two limits** of high and low noise are argued.
- **Why real diffusion models make new images.** **open**
- **Weight averaging for networks.** Only the linear case is proved.
- **Ensembles under other losses.** The split is for squared error. For
  cross-entropy the ensemble is still no worse than the average member, by
  convexity (`convexOn_logLoss` in [`CrossEntropy.lean`](../../../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean)), but that is not
  written out.
