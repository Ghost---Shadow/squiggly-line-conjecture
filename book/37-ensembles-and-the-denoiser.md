# 37. Ensembles and the ideal denoiser

**In the repository:**
[`Averaging.lean`](../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean),
note [`averaging.md`](../docs/supporting/new-inputs/averaging.md).
**You need:** chapters 11, 14, 15 and 36.

## The idea

People who enter prediction contests average the answers of several
models, and it almost always helps. People who train diffusion models
rely on a network that removes noise from an image. Both are averages,
and one fact about averages explains why the first helps and what the
second must be.

Under squared error, the best single guess for an unknown is the weighted
mean of the candidates. And the mean of several predictions has less
error than the predictions have on average, by exactly the amount they
disagree.

> The squared error of an average is the average squared error minus the
> spread. And the ideal denoiser is an attention head over the training
> set.

## An example you can do by hand

Two models predict 8 and 14 for a label of 10. Each gets share 0.5.

```
average prediction  =  0.5 × 8 + 0.5 × 14  =  11
error of the average  =  (11 − 10)²  =  1
average error  =  0.5 × (8 − 10)² + 0.5 × (14 − 10)²  =  0.5 × 4 + 0.5 × 16  =  10
spread  =  0.5 × (8 − 11)² + 0.5 × (14 − 11)²  =  0.5 × 9 + 0.5 × 9  =  9
```

And `10 − 9 = 1`. The two models are each off, by 2 and by 4, and they
are off on opposite sides. The average keeps what they agree on and loses
what they disagree on.

For the denoiser, take two training examples, 0 and 4, on a line. A noisy
input arrives at 1. With `noise_level` 1 the scores are
`−(1 − 0)² / 2 = −0.5` and `−(1 − 4)² / 2 = −4.5`. The shares are
`1 / (1 + exp(−4))`, about 0.982, and 0.018. The output is
`0.982 × 0 + 0.018 × 4`, about 0.07. Nearly the nearest example. With
`noise_level` 10 the scores are `−0.005` and `−0.045`, the shares are
about 0.51 and 0.49, and the output is about 1.96, close to the plain
average, 2.

## The statement

The ensemble. `BLEND` is the average of the predictions with the given
shares, `sum(shares[i] * predictions[i] for i in member_set)` in Python.

```lean
/-- **The error of the average is the average error minus the spread.** -/
theorem sq_blend_sub
    (shares_sum_to_one : ∑ i ∈ member_set, shares i = 1)
    (label : ℝ) :
    let blend_error   := (BLEND member_set shares predictions - label) ^ 2
    let average_error :=
      ∑ i ∈ member_set, shares i * (predictions i - label) ^ 2
    let spread        :=
      ∑ i ∈ member_set, shares i *
        (predictions i - BLEND member_set shares predictions) ^ 2
    blend_error = average_error - spread := by
```

*Read aloud:* when the shares add to one, the squared error of the blend
equals the share-weighted squared error of the members, minus the
share-weighted squared distance of the members from the blend.

The spread is a sum of squares, so it is never negative. That gives
`sq_blend_sub_le`: when the shares are also positive, the blend is at
least as good as the members are on average. The blend is also no steeper
than its steepest member (`lipschitzWith_blend`).

The ideal denoiser.

```lean
/-- The ideal denoiser for the training examples `examples` at noise level
`noise_level`. Given a noisy input `noisy_input`, each example gets a share
that falls with its squared distance from `noisy_input`, and the output is the
examples averaged with those shares. -/
noncomputable def DENOISE_IDEALLY
    (noise_level : ℝ)
    (examples : Examples → Space)
    (noisy_input : Space) : Space :=
  ATTEND (fun i => -‖noisy_input - examples i‖ ^ 2 / (2 * noise_level ^ 2))
    examples
```

*Read aloud:* the ideal denoiser is an attention head, whose query is
the noisy input, whose tokens are the training examples, and whose score
is minus the squared distance divided by twice the squared noise level.

`‖ ... ‖` is the length of a vector. `ATTEND` is the head of chapter 36.

```lean
/-- **No other guess is better.** Among all outputs `other_output`, the ideal
denoiser has the least squared distance to the examples, weighted by how
likely each is to be the clean one. -/
theorem idealDenoiser_isBest
    (noise_level : ℝ)
    (examples : Examples → Space)
    (noisy_input : Space)
    (other_output : Space) :
    let shares :=
      APPLY_SOFTMAX fun j =>
        -‖noisy_input - examples j‖ ^ 2 / (2 * noise_level ^ 2)  -- Gaussian likelihood of each example
    let denoised := DENOISE_IDEALLY noise_level examples noisy_input
    let denoiser_spread := ∑ i, shares i * ‖examples i - denoised‖ ^ 2
    let other_spread    := ∑ i, shares i * ‖examples i - other_output‖ ^ 2
    denoiser_spread ≤ other_spread := by
```

*Read aloud:* with those shares, no other output is closer to the
examples, on the share-weighted squared distance, than the ideal denoiser.

The file also has `idealDenoiser_mem_convexHull`: the output never leaves
the region the training examples span.

## Why it is true

**The ensemble.** Write the squared error of any centre as the weighted
sum of squares, minus a cross term, plus a centre term (`sum_mul_sq_sub`).
Do it twice, once with the label as the centre and once with the blend as
the centre. Both share the same sum of squares. With the blend as centre
the cross and centre terms collapse to the blend squared, so the spread is
the sum of squares minus the blend squared. Subtract that from the average
error and what is left is the squared error of the blend.

**Weight averaging.** For a model linear in its weights, averaging the
weights is averaging the lines (`liftedModel_sum_smul`). So the same
bound holds for averaged weights (`sq_liftedModel_soup_sub_le`).

**The best guess.** The weighted squared distance to any point splits
into the weighted squared distance to the weighted mean plus the squared
distance from the mean to that point (`sum_mul_norm_sub_sq`). The first
part does not depend on the point. The second is never negative and is
zero at the mean. So the mean is the best guess (`weightedMean_isBest`).
The cross term vanishes because the offsets from the mean cancel
(`sum_smul_sub_weightedMean`).

**The denoiser.** By definition (`idealDenoiser_eq_weightedMean`) it is
that weighted mean, with the softmax of the scores as shares. Apply the
best-guess result. The hull statement is `attend_mem_convexHull`.

## What it explains

**Why ensembles work.** The gain is exactly the disagreement. If the
members agree, there is nothing to gain, and if they err on different
sides, the gain is large. The spread is the variance term of chapter 43.

**What a diffusion model aims at.** With Gaussian noise, the weight of an
example falls with its squared distance from the noisy input, as the score
above says. That this is the right weight is Bayes' rule (**recalled**, not
proved here). Given it, the proof says the best possible denoiser is an
attention head over the training set.

The puzzle that follows is in the note. A denoiser that reached its target
would only return blends of its training examples, and at low noise it
would return copies. Real diffusion models make new images, so they do not
reach the target. Why they do not, and what they draw instead, is
**open**.

## How this meets the squiggly line

Through **averages** (chapter 15). The theorem says a line gets near the
data by being steep, and an average is no steeper than the steepest of
its members. Each member fits the data by being squiggly in its own way.
Between the data points the squiggles disagree and the average cancels
them. That the ensemble thereby gives back some of the slope its members
paid for is **argued**. The denoiser's shares are set by nearness
(chapter 4) to the training set.

## What is not shown

- **That the shares are the softmax above.** That is Bayes' rule with
  Gaussian noise, recalled, not proved.
- **The two limits** of high and low noise are argued, not proved.
- **Why real diffusion models make new images.** Open.
- **Weight averaging for networks.** Only the linear case is proved. For
  two weights multiplied, the midpoint between a fit and its mirror image
  outputs zero (`twoLayer_midpoint_mirror`, chapter 35).
- **Ensembles under other losses.** The split is for squared error.

## Check yourself

1. Three models predict 1, 2 and 6 for a label of 3, with shares one
   third each. What is the spread?
2. The ideal denoiser sees a noisy input exactly half way between two
   training examples, 0 and 4. What does it return?
3. Could the ideal denoiser return a point outside the stretch from the
   smallest to the largest training example?

**Answers.** (1) The blend is 3, so the error of the blend is 0. The
average error is `(4 + 1 + 9) / 3 = 14/3`. By `sq_blend_sub` the spread is
`14/3`, about 4.67. Check: `((1 − 3)² + (2 − 3)² + (6 − 3)²) / 3` is the
same. (2) The two scores are equal, so the shares are one half each, and
the output is 2 (`attend_of_const_score`). (3) No, by
`idealDenoiser_mem_convexHull`.

Previous: [36. Attention](36-attention.md) · Next: [38. Mixing: graphs, noise schedules and guidance](38-mixing.md)
