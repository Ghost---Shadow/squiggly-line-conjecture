# Dropout is weight decay

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/Supporting/Training/Dropout.lean` unless another file is named),
**argued**, **recalled**, or **open**.

## The idea

Dropout switches off a random part of the model at every training step. In
the usual form each feature is kept with probability `p` and, if kept, is
scaled up by `1 / p` so that nothing changes on average (**recalled**:
Srivastava et al. 2014).

That sounds unlike any other habit in training. For a model that is linear in
its weights, with squared error, it is weight decay under another name. The
result is known (**recalled**: Srivastava et al. 2014, section 9; Wager, Wang
and Liang 2013 for generalized linear models). Here it is proved and tied to
the rest.

## One example

Take one example. Feature `j` adds its **share** to the model's answer: the
feature times its weight. Dropout multiplies each share by a random mask.

Suppose the masks are independent, equal to one on average, and have variance
`v`. Then

```
expected squared error under dropout
    =  plain squared error  +  v × (sum of the squared shares)
```

(**proved**: `expected_dropout_loss`.) The first term is what training
without dropout would see. The second is a penalty, and it is paid by every
weight that is doing work.

The reason is the bias and variance split of
`docs/supporting/new-inputs/bias-variance.md`. The masks leave the answer
right on average and add noise around it. Squared error charges for noise,
and the noise in a sum of independent shares is the sum of their own noises.

For the usual mask the variance is `(1 − p) / p` (**proved**:
`keepMask_variance`). Keeping half the features gives `v = 1`. Keeping nine
in ten gives `v = 1/9`.

## Over the data

Add up over the examples. The penalty on weight `j` is

```
v × (weight j)² × (total squared size of feature j over the data)
```

(**proved**: `expected_dropout_loss_dataset`.) So dropout is weight decay
with a separate rate for each weight, set by how large its feature is on the
data.

If every feature has the same total squared size `c`, the penalty is `v × c`
times the squared length of the weights (**proved**:
`expected_dropout_loss_of_equal_features`). That is plain weight decay. The
Fourier features come close to this: every sine and cosine has about the same
total squared size on scattered points (**argued**).

## How this meets the squiggly line

`docs/supporting/training/weight-decay.md` shows what weight decay of
strength `μ` does: along a direction of the labels of strength `λ` it leaves
the share `μ / (λ + μ)` of the error. Directions weaker than `μ` are not
learned. Dropout does the same with `μ = v × c`.

A direction that is not learned is a long trip not taken. So dropout is a
limit on travel, set by the dropout rate.

It is also a limit on slope. A model linear in its weights is no steeper than
the size of its weights times the stretch of its lift
(`docs/networks/kernel-trick.md`). Dropout keeps the weights small, so it
keeps the line from getting squigglier than the data pays for. (**argued**)

## What is not shown

- **Decay toward zero.** The dropout penalty pulls the weights toward zero.
  `WeightDecay.lean` pulls them toward where they started. The two agree for
  a start at zero.
- **Other losses.** The identity is exact for squared error. For
  cross-entropy it holds to second order only (**recalled**: Wager, Wang and
  Liang 2013).
- **Dropout inside a deep network.** Masks on hidden units pass through
  later layers that are not linear. Nothing here covers that. **open**
- **Dropout as an average of many thinned networks.** A different account of
  the same habit (**recalled**: Srivastava et al. 2014). Not treated.
