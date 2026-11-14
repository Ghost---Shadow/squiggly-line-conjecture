# 25. Classification

**In the repository:**
[`CrossEntropy.lean`](../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean),
[`PolicyGradient.lean`](../lean/SquigglyLine/Supporting/Training/PolicyGradient.lean),
note [`cross-entropy.md`](../docs/supporting/training/cross-entropy.md).
**You need:** chapters 10, 17 and 19.

## The idea

Every chapter so far trained on squared error. Almost every classifier
in use trains on something else. Its scores go through a **softmax**,
which turns them into positive shares that add up to one, and the loss is
the **cross-entropy** of those shares against the label. With two classes
the softmax is a **sigmoid**.

The question is how much of the picture built on squared error survives.
Most of it does, for one reason. Squared error pushes each output by
"output minus label". Cross-entropy pushes each score by "prediction
minus label". The form is the same.

> The push on each score is its predicted share minus its label. So a
> classifier moves through the same kernel. What changes is that for a
> sure label no finite score is best.

## An example you can do by hand

Three classes with scores `(2, 0, 0)`. The exponentials are `e²` about
7.39, then 1 and 1, total about 9.39. The shares are about 0.787, 0.106
and 0.106. They add up to one. The label is `(1, 0, 0)`. Prediction
minus label is about `(−0.213, 0.106, 0.106)`: the first score is pushed
up and the other two down.

Two classes, label "yes". The loss is minus the log of the sigmoid of the
score.

| score | sigmoid | loss |
|---|---|---|
| 0 | 0.5 | 0.693 |
| 2 | 0.881 | 0.127 |
| 4 | 0.982 | 0.018 |

The loss keeps falling and is never zero. Now make the label soft: 0.9
in place of 1. The best score is the one whose sigmoid is 0.9, which is
`ln 9`, about 2.2. It is finite, and the loss stops falling there.

## The statement

```lean
theorem hasDerivAt_crossEntropy [Nonempty Classes]
    (labels scores direction : Classes → ℝ) :
    let rate := ∑ i, (APPLY_SOFTMAX scores i - labels i) * direction i
    HasDerivAt
      (fun fraction : ℝ =>
        GET_CROSS_ENTROPY labels fun i => scores i + fraction * direction i)
      rate 0 := by
```

*Read aloud:* move the scores a little in any direction, and the loss
changes at the rate "share minus label", summed against that direction.

`APPLY_SOFTMAX scores i` is the share of class `i`.
`GET_CROSS_ENTROPY labels scores` is the loss. `HasDerivAt f rate 0`
says `f` changes at `rate` where its input is zero. The shares are
positive and add up to one (`softmax_pos`, `sum_softmax`). For two
classes the same push is `hasDerivAt_logLoss`.

```lean
theorem map_errorStep
    (predict : Weights →L[ℝ] Outputs)
    (error_of : Outputs → Outputs)
    (learning_rate : ℝ)
    (weights : Weights) :
    let stepped_weights :=
      TAKE_ERROR_STEP predict error_of learning_rate weights
    let outputs_after  := predict stepped_weights
    let outputs_before := predict weights
    let kernel_push    :=
      predict (adjoint predict (error_of outputs_before))  -- `K e`, with `K = A A†`
    outputs_after = outputs_before - learning_rate • kernel_push := by
```

*Read aloud:* whatever rule `error_of` gives the push, one step moves the
outputs by the kernel applied to that push.

`TAKE_ERROR_STEP` is a step when the loss pushes the outputs by
`error_of outputs`. Squared error is the case "output minus label"
(`gradientStep_eq_errorStep`). Cross-entropy is the case "prediction
minus label" (`hasDerivAt_totalLogLoss`, `inner_adjoint_eq_sum`).

```lean
theorem strictAnti_logLoss_one :
    let loss_for_yes := GET_LOG_LOSS 1
    StrictAnti loss_for_yes := by
```

*Read aloud:* for the label "yes", a larger score always has a smaller
loss.

`StrictAnti` means strictly falling: a bigger input gives a smaller
output. With `logLoss_one_pos`, the loss is never zero either. With many
classes, `softmax_lt_one` and `crossEntropy_single_pos` say the same:
no share reaches one, so the loss of a sure label is never zero. For a
soft label, `logLoss_le_of_sigmoid_eq` and `exists_best_score` say the
score whose prediction equals the label is best.

Policy gradient, in reinforcement learning, is the same push.
`log_softmax_eq_neg_crossEntropy` says the log of a policy's share is
minus a cross-entropy against the label "this action was taken".
`hasDerivAt_log_policy` says its push is "action taken minus share", and
`hasDerivAt_expectedReward` says the expected reward changes at the rate:
share of each action, times its reward, times that push.

## Why it is true

**The push.** The loss is the log of the sum of the exponentials of the
scores, minus the label-weighted scores. Differentiating the log of a sum
gives each exponential over the sum, which is the share. Differentiating
the other term gives the label. Subtract.

**The kernel.** A step adds a multiple of the transpose of the model
applied to the push. The model is linear, so the outputs change by the
model applied to that. This is the argument of chapter 10, with
"output minus label" replaced by any `error_of`.

**No best score.** The slope of the loss for "yes" is the sigmoid minus
one. The sigmoid is always below one, so the slope is always negative and
the loss only falls. For a soft label the slope is the sigmoid minus the
label, which is zero where the prediction matches, and the loss is convex,
so that point is the lowest.

**Policy gradient.** The log of a share is minus the cross-entropy, so its
rate of change is that of the cross-entropy with the sign turned. The
expected reward is a sum of shares times rewards, and each share is the
exponential of its log.

## What it explains

- **A classifier is the same machine.** The same-kernel and least-travel
  results carry over. Two models with one kernel and the same start have
  the same outputs after every step, whatever the loss
  (`map_iterate_errorStep_eq`). Training reaches the nearest weights that
  give those outputs (`iterate_errorStep_is_nearest`). On a model linear
  in its weights, the cross-entropy has no hill between two settings
  (`totalLogLoss_along_le_max`).
- **Training longer means more confidence.** On data it can separate, a
  classifier's loss only falls as its scores grow, so there is no fit at
  a finite distance. The drift toward overconfidence is known
  (**recalled**: Guo et al. 2017). That it follows from the proved facts is
  **argued**.
- **Label smoothing gives the loss a floor.** This one is proved: for a
  label strictly between zero and one, a finite best score exists. Early
  stopping and weight decay do real work here too (**argued**).
- **Policy gradient is a cross-entropy step weighted by the reward**
  (**recalled**: Williams 1992).

## How this meets the squiggly line

It uses the **kernel** (chapter 10) and **travel** (chapter 9). The
theorem says a line gets near the data by being steep. For a model linear
in its weights, doubling the weights doubles every score and the slope.
A classifier trained for long on labels it can separate therefore grows
steeper without limit (**argued**). Cross-entropy is the pressure toward
a squigglier line, and the habits above are what hold it back.

## What is not shown

- **Speed.** Under squared error each direction shrinks at its own fixed
  rate. Under cross-entropy the error is not a linear function of the
  outputs, so those rates change as training goes. **Open** here.
- **Where the weights go.** On separable data the direction tends to the
  widest-margin one (**recalled**: Soudry et al. 2018). Not formalised.
- **Many classes on a model.** The statements about a model are for two
  classes. The one-example statements are for any number.
- **Policy gradient** is proved for one step only, not for a reward that
  depends on later actions.
- **Deep networks.** The kernel is fixed, as in every note here.

## Check yourself

1. Two classes with scores `(0, 0)` and the label `(1, 0)`. What is
   "prediction minus label"?
2. A classifier gives the label "yes" a score of 10. Is its loss zero?
   Could a higher score do better?
3. The label is 0.8. Which score is best, and is it finite?

**Answers.** (1) Both shares are 0.5, so it is `(−0.5, 0.5)`, by
`hasDerivAt_crossEntropy`. (2) No. By `logLoss_one_pos` the loss is
positive, about 0.000045 here. Yes: by `strictAnti_logLoss_one` a higher
score always has a smaller loss. (3) The score whose sigmoid is 0.8,
which is `ln 4`, about 1.39. It is finite, by `exists_best_score`.

Previous: [24. Symmetry: flat minima and normalisation](24-symmetry.md) · Next: [26. The perceptron, XOR and no free lunch](26-the-perceptron.md)
