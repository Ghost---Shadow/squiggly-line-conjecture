# Benign overfitting: fitting the noise without paying for it

**Proofs:** [`BenignOverfitting.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/BenignOverfitting.lean), [`Pruning.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Pruning.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/NewInputs/BenignOverfitting.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/BenignOverfitting.lean) unless another file is named),
**recalled**, or **open**.

## The idea

Big networks fit their training labels exactly, mistakes and all, and still do
well on new data (**recalled**: Zhang et al. 2017). The old advice said a model
that fits the noise must do badly. For some linear models it is now proved
that it need not: the fit can swallow the noise harmlessly
(**recalled**: Bartlett, Long, Lugosi and Tsigler 2020).

How can a model fit noise and not be hurt by it? The kernel picture gives a
short answer.

## The set-up

Split what is left to fit into two parts.

- The **signal**: the real pattern. It lies along a direction where the model
  is strong, of strength `λs`.
- The **noise**: mistakes in the labels. It lies along a direction where the
  model is weak, of strength `λe`.

There is one fit that gradient descent heads for: the nearest one. It fits
both parts exactly (**proved**: `splitFit_fits`, `splitFit_is_nearest`). That
is overfitting in the plain sense. The training error is zero and the noise
has been learned.

## What the fit does to a new input

At a new input the answer moves by two terms, one for each part:

```
signal's overlap with the new input / λs   +   noise's overlap with the new input / λe
```

(**proved**: `inner_splitFit`.) Each part is divided by the strength of its
direction. This is the whole story in one line.

The signal term is what we want. The noise term is the damage. And the damage
is divided by `λe`, the weak strength. If `λe` is tiny the damage is huge.
That is the peak of double descent: the model has barely enough strength in
the noise direction, so it pays a fortune to fit it.

## Junk features make it benign

Now give the model a pile of extra features that have nothing to do with the
task. Suppose they are spread evenly, with strength `c'` in every direction.
Strengths add (**proved** earlier: `kernel_eigen_add` in [`Pruning.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Pruning.lean)), so
every direction gains `c'`. The two terms become

```
signal's overlap / (λs + c')   +   noise's overlap / (λe + c')
```

The model still fits every label exactly. But now:

- **The damage is capped.** However weak the noise direction was, the noise
  term is at most the overlap divided by `c'`
  (**proved**: `abs_noise_damage_le`).
- **The signal is nearly untouched.** The signal term changes by at most a
  fraction `c' / λs` of itself (**proved**: `abs_signal_loss_le`).

(**proved** together: `benign_overfitting`.) So the overfitting is harmless
when `c'` sits between the two strengths: much bigger than the noise's
strength, much smaller than the signal's. The junk features take over the job
of fitting the noise on the training set. They do it cheaply, and they carry
almost none of it to new inputs.

## What had to be assumed

The cap is useful only if the new input's overlap with the noise does not grow
with the junk. That holds when a new input's junk features are unrelated to
those of the training inputs, which is what happens with many random features
(**recalled**, not proved here). The bound is stated in terms of the overlap
so the assumption is in plain sight.

## How this meets the squiggly line

More parameters put a fit nearer: that was the travel result. This note is the
same fact seen from the test set. The extra parameters shorten the trip to a
fit that includes the noise, and a short trip disturbs the function little.
Double descent is the case with too few spare parameters, where the trip is
long. Benign overfitting is the case with plenty.

## What is not shown

- **That real noise lies in weak directions.** This is the assumption that
  the signal is simple and the noise is not. **open**
- **That junk features are spread evenly.** Real extra features are not
  exactly orthogonal. **open**
- **Deep networks.** As everywhere here, the kernel is fixed. **open**
