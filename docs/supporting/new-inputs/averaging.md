# Averages: ensembles, weight averaging and the ideal denoiser

**Proofs:** [`ModeConnectivity.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/ModeConnectivity.lean), [`Averaging.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean), [`Mixing.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Mixing.lean), [`Neighbours.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Neighbours.lean), [`CrossEntropy.lean`](../../../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean).

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

## Nearness: neighbours, k-means, contrastive learning

Notes from 14 Nov 2026. Proofs in
[`lean/SquigglyLine/Supporting/NewInputs/Neighbours.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Neighbours.lean).

Three common methods use nothing but the distance between points.

- **Nearest neighbours.** To label a new input, copy the label of the
  nearest training input. If the truth has slope at most `K`, the answer is
  wrong by at most `K` times the distance to that input (**proved**:
  `abs_sub_nearest_le`). This is the theorem of this project read the other
  way: how far the data is from the query, times slope, is the error.
- **k-means.** The cost is the summed squared distance from each point to
  its centre. A step has two halves. Give every point a centre no further
  than the one it had, and the cost does not rise (**proved**:
  `sum_sq_reassign_le`). Move a centre to the mean of its points, and no
  other place for it has a lower cost (**proved**: `sum_sq_mean_le`, from
  `weightedMean_isBest`). So the cost never rises. Vector quantisation is
  the first half used as a layer.
- **Contrastive learning.** The loss is a softmax over the cosine
  similarity of a query with each key, divided by a temperature `τ`. For
  vectors of length one, the dot product is one minus half the squared
  distance (**proved**: `inner_eq_one_sub_of_unit`), and adding the same
  number to every score changes no share (**proved**: `softmax_add_const`).
  So the shares are those of a softmax over minus the squared distance,
  divided by `2τ` (**proved**: `softmax_cosine_eq_softmax_distance`). Those
  are the shares of the ideal denoiser above, with noise level `√τ`. A
  contrastive loss scores pairs by nearness, and its temperature is a
  width.

Not shown: what the contrastive loss does to the lift as it trains, and
that k-means stops.

## More averages, and one thing that is not

Notes from 14 Nov 2026. Proofs in
[`lean/SquigglyLine/Supporting/NewInputs/Mixing.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Mixing.lean).

- **Graph networks.** A message-passing layer replaces each node by a
  weighted sum of the nodes. If each node's weights add to one and every
  weight is at least `m`, two nodes end no further apart than `1 - n m`
  times the range of the values, for `n` nodes (**proved**:
  `abs_messagePassing_sub_le`). After `L` layers the factor is
  `(1 - n m)^L` (**proved**: `abs_iterate_messagePassing_sub_le`). This is
  the blurring of deep graph networks, and it is the same statement as the
  merging of tokens under attention. On a real graph a node gives weight
  only to its neighbours, so the floor holds only after enough layers for
  every node to reach every other; that step is not shown.
- **The diffusion noising schedule.** Follow the share of the variance that
  is signal and the share that is noise. A step keeps `1 - β` of each and
  adds `β` of fresh noise. The two shares still add to one (**proved**:
  `noisingStep_sum`), and after `n` steps the signal's share is
  `(1 - β)^n` of what it was (**proved**: `iterate_noisingStep_signal`).
  The forward process is an average of the data with noise, with the
  weight on the data shrinking geometrically.
- **Data augmentation.** Average a model over a group of moves of the
  input, such as shifts or flips. The averaged model gives the same answer
  before and after any of the moves (**proved**: `averageOverMoves_smul`).
  If the moves keep distances it is no steeper than the model it was made
  from (**proved**: `lipschitzWith_averageOverMoves`). Training on
  augmented data pushes toward this average (**argued**).
- **The baseline.** In policy gradient the push on the score of an action
  is "action taken minus prediction", times the reward. Averaged over the
  action taken, "action taken minus prediction" is zero (**proved**:
  `sum_mul_baseline_eq_zero`). So subtracting the same baseline from every
  reward leaves the average push as it was (**proved**:
  `sum_mul_sub_baseline`). That it lowers the noise is not shown.
- **Classifier-free guidance.** The guided prediction is `1 + w` of the
  prediction with the prompt minus `w` of the prediction without. It moves
  from the plain prediction toward the prompt, `1 + w` times as far as the
  prompt alone does (**proved**: `guidance_sub`, `norm_guidance_sub`). For
  `w > 0` it is not on the stretch between the two predictions
  (**proved**: `guidance_notMem_segment`). One weight is negative, so this
  is not an average. It is the one step of a diffusion sampler that can
  leave the region the examples span.

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
