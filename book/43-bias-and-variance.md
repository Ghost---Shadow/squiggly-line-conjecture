# 43. Bias and variance

**In the repository:**
[`BiasVariance.lean`](../lean/SquigglyLine/Supporting/NewInputs/BiasVariance.lean),
note [`bias-variance.md`](../docs/supporting/new-inputs/bias-variance.md).
**You need:** chapters 10, 16 and 42. Chapter 44 follows on from this one.

## The idea

The oldest rule about model size is the **bias and variance trade-off**
(**recalled**: Geman, Bienenstock and Doursat 1992). A model that is too
stiff misses the pattern. That miss is the **bias**. A model that is too
loose follows the noise in its training labels. That is the **variance**.
The best model sits in between.

Double descent (chapter 10) seemed to break the rule, because very loose
models do well. The kernel picture keeps the rule, and shows what it
turns on. It is not the size of the model. It is a **floor** added to the
strength of every direction (chapter 10 called the strength of a
direction `strength`). A floor can come from weight decay, from stopping
early, or from spare parameters.

At a new input, a fit with a floor is off from the ideal answer by two
terms. One does not depend on the noise: the bias. One does: it carries
the noise, and its square, averaged over the draws of the noise, is the
variance.

> The expected squared error at a new input is exactly the bias squared
> plus the variance. Raising the floor raises the bias and lowers the
> variance.

## An example you can do by hand

Take a signal that has overlap 6 with the new input, along a direction of
strength 3. The right answer is `6 / 3 = 2`. Take noise along a direction
of strength 1, whose overlap with the new input is `+1` or `−1` with
equal chance, so it is zero on average.

With a floor of 1, the fit divides by the raised strengths. The signal
term is `6 / (3 + 1) = 1.5`. It is 0.5 below the right answer. The bias
factor is `1 / (3 + 1) = 0.25`, and `2 × 0.25 = 0.5`, so the bias is
`−0.5`. The noise term is `±1 / (1 + 1) = ±0.5`.

- Noise `+1`: the answer is `1.5 + 0.5 = 2`. The error is 0.
- Noise `−1`: the answer is `1.5 − 0.5 = 1`. The error is `−1`.

The mean of the squared errors is `(0 + 1) / 2 = 0.5`. The split says
`bias² + variance = 0.5² + 1 / 2² = 0.25 + 0.25 = 0.5`. It agrees.

Now move the floor.

| floor | bias | variance | bias² + variance |
|---|---|---|---|
| 0 | 0 | 1 | 1 |
| 1 | −0.5 | 0.25 | 0.5 |
| 3 | −1 | 0.0625 | 1.0625 |

At floor 3 the signal term is `6 / 6 = 1`, so the bias is `−1`. The noise
term is `±1 / 4`, so the variance is `1 / 4² = 0.0625`. The bias grows
down the table and the variance shrinks. Their sum falls and then rises.
That is the old U-shaped curve, with the floor as its dial.

## The statement

The bias first. A floor shrinks the signal term by a fixed fraction.

```lean
theorem signal_term_sub
    (signal_overlap : ℝ)
    {signal_strength : ℝ}
    {floor : ℝ}
    (signal_strength_ne_zero : signal_strength ≠ 0)                -- so that the divisions below make sense
    (raised_strength_ne_zero : signal_strength + floor ≠ 0) :
    let true_signal_term   := signal_overlap / signal_strength     -- the right answer: the overlap over the strength
    let fitted_signal_term :=
      signal_overlap / (signal_strength + floor)                   -- the fit divides by the strength with the floor added
    let bias_factor        := GET_BIAS_FACTOR signal_strength floor
    fitted_signal_term - true_signal_term
      = -(true_signal_term * bias_factor) := by                    -- minus: the floor pulls the answer towards zero
```

*Read aloud:* with a floor, the signal term comes out too small by the
right answer times `floor / (signal_strength + floor)`.

`GET_BIAS_FACTOR signal_strength floor` is that fraction. It is 0 with no
floor and close to 1 with a very high one. In the example it was 0.25.

Now the two parts together.

```lean
theorem bias_variance
    {noise_part : NoiseTerm Outcomes}
    (noise_part_has_mean : Integrable noise_part noise_distribution)  -- `Integrable`: its average exists
    (noise_part_sq_has_mean :
      Integrable (fun outcome => noise_part outcome ^ 2)
        noise_distribution)
    (noise_part_mean_zero :
      ∫ outcome, noise_part outcome ∂noise_distribution = 0)       -- `∫ ... ∂`: the average over the draws of the noise
    (bias : ℝ) :
    let mean_squared_error :=
      ∫ outcome, (bias + noise_part outcome) ^ 2 ∂noise_distribution
    let variance           :=
      ∫ outcome, noise_part outcome ^ 2 ∂noise_distribution        -- the mean is zero, so the mean square is the variance
    mean_squared_error = bias ^ 2 + variance := by                 -- the cross term `2 * bias * noise_part` averages to zero
```

*Read aloud:* if the noise part is zero on average, the average of
`(bias + noise_part) ^ 2` is `bias ^ 2` plus the average of
`noise_part ^ 2`.

A `NoiseTerm` is a number that depends on the random draw of the noise.
The symbol `∫ ... ∂noise_distribution` is the average of what is written
over all those draws. The first two assumptions only say that the
averages exist.

Three more results finish the picture. `expected_sq_error` applies
`bias_variance` to the fit with a signal and a noise, and gives the
variance as the mean square of the noise overlap divided by
`(noise_strength + floor) ^ 2`. `bias_factor_mono` says a higher floor
gives a larger bias factor, for a positive `signal_strength`.
`variance_factor_anti` says a higher floor gives a smaller
`1 / (noise_strength + floor)`, so the noise is divided by more.

## Why it is true

**The bias.** Subtract the two fractions. The difference of
`signal_overlap / (signal_strength + floor)` and
`signal_overlap / signal_strength` is the right answer times
`floor / (signal_strength + floor)`, with a minus sign. It is algebra
with a common denominator.

**They add.** Multiply out `(bias + noise_part) ^ 2`. It is `bias ^ 2`,
plus `2 × bias × noise_part`, plus `noise_part ^ 2`. Average the three
terms one at a time. The first is a constant. The last is the variance.
The middle one is a constant times the average of the noise part, and
that average is zero. So the cross term vanishes.

**The dial.** In `expected_sq_error` the error is the bias plus the noise
divided by its raised strength. Dividing a random number by a fixed one divides its mean
square by the square of the fixed one, which gives the variance above. The two monotone
results are comparisons of fractions with the floor in the denominator.

## What it explains

The trade-off is real, and its dial is the floor. A high floor gives a
stiff model: it shrinks the pattern along with the noise. A low floor
gives a loose one: it keeps the pattern and lets the noise through at
full size.

Why does double descent not break the rule? The classical U-shaped curve
is what you see when model size acts only as the floor. But size also
changes the strengths. With barely enough parameters the noise direction
is very weak, `noise_strength` is tiny, the floor is near zero, and the
variance `1 / (noise_strength + floor) ^ 2` is large. That is the peak.
More parameters raise the floor again through spare features, and the
variance comes down. This account is **argued** from the formulas above
and from the travel peak of chapter 10. That a real sweep of model size
moves the strengths and the floor this way is **measured** there for one
model, and is not proved.

So there is one trade-off and two ways of moving along it. The old rule
describes the first. Double descent shows the second.

## How this meets the squiggly line

This uses the **travel** of chapter 9 and the **kernel** of chapter 10.
Variance is the cost of a long trip: fitting noise along a weak direction
means moving far in parameter space, and the function is disturbed
everywhere. Bias is the cost of refusing the trip. The floor sets how
long a trip the model will take.

## What is not shown

The proofs are for a **fixed kernel**, with **one signal direction and
one noise direction**.

- **Many directions.** With many, each direction has its own two terms.
  This is not written out.
- **Bias from the wrong model.** Bias here comes only from the floor. A
  model that cannot express the pattern at all has a further bias that
  this account leaves out.
- **Deep networks.** The kernel is fixed. **open**

## Check yourself

1. The bias is 2 and the noise part is `+1` or `−1` with equal chance.
   What is the expected squared error?
2. A signal has strength 3. The floor goes from 1 to 2. What happens to
   the bias factor? A noise direction has strength 1. What happens to
   `1 / (noise_strength + floor)`?
3. Suppose the noise part were always `+1`. Would
   `bias ^ 2 + variance` still equal the mean squared error when the
   bias is 1?

**Answers.** (1) The two outcomes are `(2 + 1) ^ 2 = 9` and
`(2 − 1) ^ 2 = 1`, which average to 5. The split gives `2 ^ 2 + 1 = 5`,
as `bias_variance` says. (2) The bias factor `floor / (signal_strength +
floor)` goes from `1 / 4 = 0.25` to `2 / 5 = 0.4`, so it rises, as
`bias_factor_mono` says. The other quantity goes from `1 / 2` to `1 / 3`,
so it falls, as `variance_factor_anti` says. (3) No. The mean squared
error is `(1 + 1) ^ 2 = 4`, and `bias ^ 2 + variance = 1 + 1 = 2`. The
theorem needs `noise_part_mean_zero`, and here the mean is 1, so the
cross term does not vanish.

Previous: [42. Same kernel, same predictions](42-same-kernel.md) · Next: [44. Benign overfitting](44-benign-overfitting.md)
