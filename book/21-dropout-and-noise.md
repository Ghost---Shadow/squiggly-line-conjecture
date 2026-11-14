# 21. Dropout, noise and other regularisers

**In the repository:**
[`Dropout.lean`](../lean/SquigglyLine/Supporting/Training/Dropout.lean),
[`Regularisers.lean`](../lean/SquigglyLine/Supporting/Training/Regularisers.lean),
notes [`dropout.md`](../docs/supporting/training/dropout.md) and
[`weight-decay.md`](../docs/supporting/training/weight-decay.md).
**You need:** chapters 10, 13 and 20.

## The idea

**Dropout** switches off a random part of the model at every training
step. In the usual form each feature is kept with probability
`keep_probability`, and if kept it is scaled up by `1 / keep_probability`,
so that nothing changes on average (**recalled**: Srivastava et al.
2014). That sounds unlike weight decay. For a model that is linear in its
weights, with squared error, it is weight decay under another name. This
is known (**recalled**: Srivastava et al. 2014, section 9; Wager, Wang
and Liang 2013). Here it is proved.

The same idea works for other habits that add noise or a nudge. Each one
turns out to be a charge on slope, or a floor on travel, as in chapter
20.

> Under dropout, the expected squared error is the plain squared error
> plus a penalty: the variance of the mask times the sum of the squared
> shares of the features.

## An example you can do by hand

One example with label 4. Two features, and the model's answer is the
sum of two **shares** (a feature times its weight). The shares are 3 and
1, so with no dropout the answer is 4 and the plain error is 0.

Keep each feature with probability `1 / 2`. Each mask is then 0 or 2 with
equal chance. Its mean is 1, and its variance is
`(1 − 1/2) / (1/2) = 1`. The four outcomes are equally likely:

| masks | answer | squared error |
|---|---|---|
| 0, 0 | 0 | 16 |
| 0, 2 | 2 | 4 |
| 2, 0 | 6 | 4 |
| 2, 2 | 8 | 16 |

The mean squared error is `(16 + 4 + 4 + 16) / 4 = 10`. The formula says
`0 + 1 × (3² + 1²) = 10`. It matches. With keep probability `9 / 10` the
variance is `(1/10) / (9/10) = 1/9`, and the penalty is `10 / 9`.

Noise on the input works the same way. Take the line `2 × input` at
input 1 with label 2, and add noise of `+0.5` or `−0.5` with equal
chance. The spread is 0.5. The answers are 3 and 1, both off by 1, so
the mean squared error is 1. The formula says `0 + 0.5² × 2² = 1`.

## The statement

```lean
/-- **Dropout adds a penalty.** One example with label `label`. Feature `j`
contributes the share `shares j` (the feature times its weight) to the
answer, and dropout multiplies it by `mask j`. If the masks are independent,
one on average and of variance `mask_variance`, the expected squared error is
the plain squared error plus `mask_variance` times the sum of the squared
shares. -/
theorem expected_dropout_loss
    {mask : RandomMask Features Outcomes}
    (masks_are_square_integrable :
      ∀ feature, MemLp (mask feature) 2 probability)  -- each mask has a finite average and variance, so the averages below exist
    (masks_are_independent : ARE_MASKS_INDEPENDENT probability mask)  -- so that the variances of the shares add up
    (masks_are_one_on_average : ARE_MASKS_ONE_ON_AVERAGE probability mask)
    {mask_variance : ℝ}
    (masks_have_this_variance :
      ARE_MASKS_OF_VARIANCE probability mask mask_variance)
    (label : ℝ)
    (shares : Features → ℝ) :
    let expected_dropout_loss :=
      GET_AVERAGE probability fun outcome =>
        let noisy_answer := ∑ j, mask j outcome * shares j  -- each share, multiplied by its mask
        (label - noisy_answer) ^ 2
    let plain_loss := (label - ∑ j, shares j) ^ 2           -- the squared error with no dropout
    let penalty    := mask_variance * ∑ j, shares j ^ 2     -- the variance of the noisy answer: independent variances add
    expected_dropout_loss = plain_loss + penalty := by      -- mean of a square = square of the mean + variance
```

*Read aloud:* when the masks are independent, average to one and have
variance `mask_variance`, the average squared error is the plain squared
error plus `mask_variance` times the sum of the squared shares.

`probability` says how likely each random draw is. `GET_AVERAGE` is the
average over those draws. The first hypothesis only says the averages
exist.

Two more results turn this into weight decay. Over a whole set of
examples, the penalty on weight `j` is its square times the total squared
size of feature `j` over the data (`expected_dropout_loss_dataset`). If
every feature has the same total squared size `feature_size`, the
penalty is `mask_variance × feature_size` times the squared length of the
weights (`expected_dropout_loss_of_equal_features`). That is weight decay
of chapter 20 with `decay_strength = mask_variance × feature_size`. The
usual mask has variance `(1 − keep_probability) / keep_probability`
(`keepMask_variance`).

```lean
/-- **Noise on the input is a charge on slope.** Average the squared error of
the line `slope * input` over input noise of mean zero and spread
`noise_spread`. The result is the plain squared error plus
`noise_spread² * slope²`. -/
theorem sum_mul_sq_sub_noisy_eq
    {chances noises : Outcomes → ℝ}
    {noise_spread : ℝ}
    (chances_sum_to_one : ∑ j, chances j = 1)
    (noise_has_mean_zero : ∑ j, chances j * noises j = 0)
    (noise_has_variance :
      ∑ j, chances j * noises j ^ 2 = noise_spread ^ 2)
    (slope input label : ℝ) :
    let noisy_error := ∑ j,
      chances j * (label - slope * (input + noises j)) ^ 2
    let plain_error := (label - slope * input) ^ 2
    let noise_charge := noise_spread ^ 2 * slope ^ 2
    noisy_error = plain_error + noise_charge := by
```

*Read aloud:* noise on the input adds `noise_spread²` times `slope²` to
the average squared error.

The slope of the line `slope × input` is `slope`, so this is a charge on
slope, the currency of chapter 3.

```lean
/-- **Lasso sets a weak direction to exactly zero.** If the target is no larger
than the penalty, the best weight is zero. -/
theorem lassoCost_zero_le
    {penalty target : ℝ}
    (target_within_penalty : |target| ≤ penalty)
    (weight : ℝ) :
    let zero_cost := GET_LASSO_COST penalty target 0
    let cost      := GET_LASSO_COST penalty target weight
    zero_cost ≤ cost := by
```

*Read aloud:* if the target is no bigger than the penalty, weight zero
costs no more than any other weight.

`GET_LASSO_COST penalty target weight` is half the squared miss of the
target plus `penalty` times the size of the weight. Weight decay, with
`GET_RIDGE_COST`, uses the square of the weight instead. By
`ridgeCost_div_le` its best weight is `target / (1 + penalty)`, which is
zero only when the target is. By `lassoCost_sub_le`, a target above the
penalty is kept, shortened by exactly the penalty.

## Why it is true

**Dropout.** The masks leave the answer right on average, so the mean of
the answer is the sum of the shares. Their variances add, because the
masks are independent, and each share's variance is `mask_variance` times
the share squared. Now use the old fact that the mean of a square is the
square of the mean plus the variance. Applied to the error, that is the
plain loss plus the penalty. These are `mean_of_answer`,
`variance_of_answer` and `variance_of_error` in the proof.

**Noise.** Expand the square. The cross term has a factor that averages
to zero. The last term is the spread squared times the slope squared.

**Lasso.** The pull of the target on the weight is at most
`penalty × |weight|` when the target is within the penalty. The quadratic
then cannot beat zero.

## What it explains

Dropout needs no separate story. For squared error it is weight decay,
with a rate set by the dropout rate and the size of the features, and
chapter 20 says what weight decay does: patterns weaker than the penalty
are not learned. The note also reads other habits as charges.

- **Adversarial training.** No nudge of size at most `size_limit` on
  each input lowers a linear score by more than `size_limit` times the
  summed sizes of the weights (`sub_le_score_add`), and one nudge
  lowers it by exactly that (`score_add_worst_nudge`). With a nudge of
  0.1 and weights 2 and −3, the score drops by `0.1 × 5 = 0.5`.
- **Stochastic depth.** Keep a residual branch with chance `keep_chance`.
  On average the layer is the input plus `keep_chance` times the branch
  (`mean_stochasticDepth`). With chance 0.8, input 5 and branch 10 that
  is `5 + 8 = 13`.
- **Mixup.** A model that fits every blend of two examples is straight
  between them (`mixup_fit_gap`), so it has the least slope that any
  line through both can have (`abs_sub_le_of_lipschitz_fit`).
- **Distillation.** Against a teacher's soft label, the teacher's own
  score is a best score (`logLoss_teacher_le`). A hard label has none.

## How this meets the squiggly line

Every item above is a limit on slope or on travel. Noise and adversarial
nudges charge slope directly: chapter 3 says a model buys nearness with
slope, and these charges make slope cost something. Dropout keeps the
weights small, and a model linear in its weights is no steeper than the
size of its weights times the stretch of its lift (chapter 11). That
last step is **argued** in the note, not proved here.

## What is not shown

- These are statements for a model linear in its weights, with squared
  error and a fixed kernel.
- The dropout penalty pulls the weights towards zero. Chapter 20's decay
  pulls them towards where they started. The two agree for a start at
  zero.
- For cross-entropy the dropout identity holds to second order only
  (**recalled**: Wager, Wang and Liang 2013). Dropout inside a deep
  network is **open**. Lasso is shown for one weight, not many.
- That Fourier features have nearly equal total size on scattered points,
  which makes dropout close to plain weight decay there, is **argued**.

## Check yourself

1. Keep probability is `1 / 4`. What is the mask variance? With shares 2
   and 2 and a label of 4, what is the expected squared error?
2. Noise of spread 0.1 is added to the input of a line of slope 5. What
   is the charge?
3. Penalty 1 and target 0.8. What is the best weight for lasso? For weight
   decay?

**Answers.** (1) By `keepMask_variance`, `(1 − 1/4) / (1/4) = 3`. The plain
error is 0, so by `expected_dropout_loss` the penalty is
`3 × (2² + 2²) = 24`. (2) `0.1² × 5² = 0.25`, by `sum_mul_sq_sub_noisy_eq`.
(3) Lasso gives 0, since `0.8 ≤ 1` (`lassoCost_zero_le`). Weight decay
gives `0.8 / (1 + 1) = 0.4`, by `ridgeCost_div_le`.

Previous: [20. Weight decay and early stopping](20-weight-decay-and-early-stopping.md) · Next: [22. Batches, small steps and budgets](22-batches-steps-and-budgets.md)
