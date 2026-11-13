# Weight decay, early stopping and spare parameters are one thing

**Proofs:** [`Regularisers.lean`](../../../lean/SquigglyLine/Supporting/Training/Regularisers.lean), [`SpectralBias.lean`](../../../lean/SquigglyLine/Supporting/Training/SpectralBias.lean), [`WeightDecay.lean`](../../../lean/SquigglyLine/Supporting/Training/WeightDecay.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/Training/WeightDecay.lean`](../../../lean/SquigglyLine/Supporting/Training/WeightDecay.lean) unless another file is named),
**recalled**, or **open**.

## The idea

Three habits are used to keep a model from fitting noise.

- **Weight decay.** Pull the weights back a little at every step.
- **Early stopping.** Stop training before the loss reaches zero.
- **Spare parameters.** Use a model much bigger than the data needs.

It is common knowledge that the first two act alike
(**recalled**: for example Goodfellow, Bengio and Courville 2016, section 7.8).
For a model that is linear in its weights all three can be put in one
formula, and the formula is short.

## Weight decay

Add to the loss a penalty `μ` on how far the weights are from where they
started. Follow a direction of the labels of strength `λ`. Training then comes
to rest at a point that does not fit the labels exactly. It leaves a share of
the error:

```
share of the error left  =  μ / (λ + μ)
```

(**proved**: `residual_ridgeFit`, and `decayStep_ridgeFit` shows it is where
gradient descent with weight decay rests.) A strong direction, `λ` much bigger
than `μ`, is fitted almost fully. A weak one, `λ` much smaller than `μ`, is
left almost alone. So `μ` is a cut-off: directions weaker than `μ` are not
learned.

## Weight decay is spare parameters

At a new input, the weight-decay fit moves the answer by

```
overlap with the new input / (λ + μ)
```

(**proved**: `inner_ridgeFit`.) This is the formula from
`docs/supporting/new-inputs/benign-overfitting.md`, where a pile of junk features of strength `c'` gave
`overlap / (λ + c')`. The two are the same with `c' = μ`.

So a big model with many spare features behaves like a small model with
weight decay. The spare features add the same amount to every direction, and
that amount acts as the penalty. This is why very large models often need
little explicit regularisation.

## Early stopping is weight decay

Now use no penalty and stop after `t` steps. The share of the error left along
the direction is `(1 − ηλ)^t` (**proved** earlier: [`SpectralBias.lean`](../../../lean/SquigglyLine/Supporting/Training/SpectralBias.lean)). It is
caught between two numbers:

```
1 − t·ηλ   ≤   share left after t steps   ≤   1 / (1 + t·ηλ)
```

(**proved**: `one_sub_mul_le_pow_one_sub` earlier, `early_stopping_le_ridge`
here.) The right-hand number is exactly the share that weight decay leaves
when its penalty is `μ = 1 / (ηt)` (**proved**: `ridge_share_eq`).

So stopping after `t` steps cuts every direction at least as hard as weight
decay of strength `1 / (ηt)`, and in the same order: strong directions kept,
weak ones cut. Training for longer is the same as turning the penalty down.

## The one formula

All three add a floor to the strength of every direction:

| Habit | What is added to `λ` |
|---|---|
| Weight decay `μ` | `μ` |
| Stopping after `t` steps | about `1 / (ηt)` |
| Spare features of strength `c'` | `c'` |

A direction weaker than the floor is not learned and does little harm. A
direction stronger than the floor is learned almost as before.

## Other regularisers, in the same terms

Notes from 14 Nov 2026. Proofs in
[`lean/SquigglyLine/Supporting/Training/Regularisers.lean`](../../../lean/SquigglyLine/Supporting/Training/Regularisers.lean).

Weight decay is a floor on travel. The other common regularisers are either
the same floor in another shape or a direct charge on slope.

- **Lasso.** Charge `μ` times the size of a weight, not its square. For one
  weight with target `a`: if `a` is no larger than `μ` the best weight is
  exactly zero (**proved**: `lassoCost_zero_le`), and if it is larger the
  best weight is `a - μ` (**proved**: `lassoCost_sub_le`). Weight decay's
  best weight is `a / (1 + μ)`, which is zero only when `a` is (**proved**:
  `ridgeCost_div_le`). So weight decay shrinks a weak direction and lasso
  does not travel along it at all.
- **Noise on the input.** For the line `w * x`, average the squared error
  over input noise of mean zero and variance `σ²`. The result is the plain
  squared error plus `σ² * w²` (**proved**: `sum_mul_sq_sub_noisy_eq`). The
  weight of a line is its slope, so noise on the input is a charge on slope.
- **Adversarial training.** For a linear model, no nudge of size at most `ε`
  on each input lowers the score by more than `ε` times the summed sizes of
  the weights (**proved**: `sub_le_score_add`), and one nudge lowers it by
  exactly that (**proved**: `score_add_worst_nudge`). Training against the
  worst nudge is training with that penalty. The summed sizes of the
  weights are the slope of the model when distance is measured by the
  largest change in any one input.
- **Stochastic depth.** Keep a residual branch with chance `p` and drop it
  otherwise. On average the layer is the input plus `p` times the branch
  (**proved**: `mean_stochasticDepth`).
- **Mixup.** Train on blends of two examples, with the labels blended the
  same way. A model that fits every blend is straight between the two: the
  gap in its output between two blends is the gap in labels times the share
  of the way between them (**proved**: `mixup_fit_gap`). Any line through
  both examples has at least that slope (**proved**:
  `abs_sub_le_of_lipschitz_fit`). So mixup asks for the least slope a fit
  can have between examples.
- **Distillation.** Train a student on a teacher's soft label. Against that
  label the teacher's own score is a best score (**proved**:
  `logLoss_teacher_le`). A hard label has no best score
  (`cross-entropy.md`). So a student is never asked for more slope than its
  teacher has.

Not shown: lasso for many weights at once, any of these for a deep
network, and the noise or adversarial penalty under cross-entropy.

## How this meets the squiggly line

The floor is a limit on travel. Fitting a weak direction means a long trip in
parameter space, and a long trip disturbs the function everywhere (see
`docs/networks/double-descent.md`). Each of the three habits refuses the long trips and
takes the short ones.

## What is not shown

- **Decay towards zero.** The penalty here pulls towards the starting weights.
  With a start at zero that is ordinary weight decay. Otherwise the two
  differ.
- **Several directions at once.** The statements follow one direction of the
  labels. Because everything is linear the directions add up, but that sum is
  not written out here.
- **Adaptive methods.** Weight decay inside Adam behaves differently. That
  is proved, for Adam with no memory, in `step-rules.md` under AdamW.
- **Deep networks.** The kernel is fixed, as everywhere in these notes.
  **open**
