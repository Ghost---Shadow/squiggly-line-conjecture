# Bias and variance, and what the dial is

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/BiasVariance.lean` unless another file is named),
**recalled**, **argued**, or **open**.

## The idea

The oldest rule about model size is the bias and variance trade-off
(**recalled**: Geman, Bienenstock and Doursat 1992). A model that is too stiff
misses the pattern: that is bias. A model that is too loose follows the noise:
that is variance. The best model sits in between.

Double descent seemed to break this rule, because very loose models do well.
The kernel picture keeps both. It shows what the trade-off really turns on,
and it is not the size of the model.

## The split

Take the set-up of `benign-overfitting.md`. What is left to fit is a signal
along a strong direction, of strength `λs`, plus noise along a weak one, of
strength `λe`. A floor `μ` is added to every direction. By `weight-decay.md`
the floor can come from weight decay, from stopping early, or from spare
parameters.

At a new input the fit is off from the ideal answer by two terms:

```
error  =  − (signal's overlap / λs) × μ / (λs + μ)   +   noise's overlap / (λe + μ)
```

(**proved**: `signal_term_sub` gives the first term, and the second is the
noise term of `inner_splitFit`.) The first term is there even with no noise.
It is the bias. The second is there only because of the noise. Squared and
averaged, it is the variance.

**They add.** If the noise is zero on average, the expected squared error is
exactly the bias squared plus the variance:

```
expected squared error  =  bias²  +  variance
```

(**proved**: `bias_variance` in general, `expected_sq_error` for this
set-up.) There is no cross term, because the noise averages out against a
fixed bias.

## The dial is the floor

- **Raising the floor raises the bias.** The factor `μ / (λs + μ)` grows with
  `μ` (**proved**: `bias_factor_mono`).
- **Raising the floor lowers the variance.** The factor `1 / (λe + μ)` falls
  with `μ` (**proved**: `variance_factor_anti`).

So the trade-off is real, and its dial is `μ`. A high floor gives a stiff
model: it shrinks the pattern along with the noise. A low floor gives a loose
one: it keeps the pattern and lets the noise through at full size.

## Why double descent does not break it

The classical U-shaped curve is what you see when model size acts only as the
floor. But size also changes the strengths. With barely enough parameters the
noise direction is very weak, `λe` is tiny, the floor is near zero, and the
variance `1 / (λe + μ)²` is enormous. That is the peak. Adding more parameters
raises the floor again, through spare features, and the variance comes back
down. **argued** from the formula above and the travel peak in
`double-descent.md`; that a real sweep of model size moves `λe` and `μ` this
way is **measured** there for one model and is not proved.

So there is one trade-off and two ways of moving along it. The old rule
describes the first. Double descent shows the second.

## How this meets the squiggly line

Variance is the cost of a long trip. Fitting noise along a weak direction
means moving far in parameter space, and the function is disturbed
everywhere. Bias is the cost of refusing the trip. The floor `μ` sets how long
a trip the model will take.

## What is not shown

- **Many directions.** The split is written for one signal direction and one
  noise direction. With many, each direction has its own two terms.
- **Bias from the wrong model.** Bias here comes only from the floor. A model
  that cannot express the pattern at all has a further bias that this account
  leaves out.
- **Deep networks.** The kernel is fixed. **open**
