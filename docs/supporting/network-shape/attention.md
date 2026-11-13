# Attention: a weighted average, and one step of training

**Proofs:** [`Depth.lean`](../../../lean/SquigglyLine/Networks/Depth.lean), [`MarkovChains.lean`](../../../lean/SquigglyLine/Networks/MarkovChains.lean), [`Attention.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/Attention.lean), [`SkipAndNorm.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/SkipAndNorm.lean), [`CrossEntropy.lean`](../../../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/NetworkShape/Attention.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/Attention.lean) unless another file is named),
**argued**, **recalled**, or **open**.

## The idea

A transformer is built from attention heads. One head does three things for
each query.

- **Score.** Give every token a score against the query.
- **Share.** Turn the scores into shares with a softmax. The shares are
  positive and add up to one (**proved**: `softmax_pos`, `sum_softmax` in
  [`CrossEntropy.lean`](../../../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean)).
- **Average.** Return the tokens' values, averaged with those shares.

Two things can be said about this with the tools already here. Attention on
its own cannot make anything squigglier. And one head, read the right way, is
one step of training.

## Attention is an average

A weighted average of some values lies among them. So if every value sits
inside a region with no dents, the output sits inside it too (**proved**:
`attend_mem_of_convex`, `attend_mem_convexHull`).

Three consequences.

- **Merged stays merged.** If every token carries the same value, every query
  gets that value back, whatever the scores (**proved**: `attend_const`).
  This is the rule of [`MarkovChains.lean`](../../../lean/SquigglyLine/Networks/MarkovChains.lean) again.
- **At the start it is the plain average.** With equal scores every token
  gets the same share (**proved**: `softmax_const`, `attend_of_const_score`).
  A fresh head with scores near zero is close to this.
- **Depth does not help.** Stack any number of attention layers, with scores
  that may depend on the tokens in any way. Every token stays inside any
  dent-free region that held all the tokens at the start (**proved**:
  `iterate_attentionLayer_mem`).

The shares in one layer form a table with positive rows that each add up to
one. That is the table of a Markov chain on the tokens (**argued**: it is the
definition). An attention layer is one step of that chain, and chains of this
kind pull their states together. A transformer made of attention alone is
known to lose the differences between its tokens very fast with depth
(**recalled**: Dong, Cordonnier and Loukas 2021).

## Attention is one step of training

Take a model linear in its weights, starting from zero. Give it some examples
and one step of gradient descent. Its prediction at a new input is

```
step size × Σ (overlap of example i with the new input) × (label of example i)
```

(**proved**: `inner_gradientStep_zero`.) Now read that as an attention head.
The tokens are the examples. The score of a token is its overlap with the
query. Its value is its label. Leave out the softmax. Then the head's output
is that prediction (**proved**: `prediction_one_step_eq_linearAttention`).

A second step does the same with one change: each example's value is the
error still left on it (**proved**: `prediction_step_eq_linearAttention`).

So a stack of such heads can run gradient descent on the examples in its
prompt, one step per layer, without changing any of its own weights. This is
the simplest account of in-context learning (**recalled**: von Oswald et al.
2023). The overlap used as the score is the kernel of
`docs/networks/kernel-trick.md`.

With the softmax kept, the head is a weighted average of the labels of the
examples most like the query. Statisticians call that kernel smoothing
(**recalled**: Nadaraya 1964, Watson 1964).

## How this meets the squiggly line

The theorem says a line gets near the data by being steep. An average is
never steeper than what it averages, so attention cannot supply the slope.
In a transformer the squiggle has to come from the other parts: the
feed-forward layers, which are the ReLU folds of [`Depth.lean`](../../../lean/SquigglyLine/Networks/Depth.lean), and the skip
connections, which keep the tokens apart ([`SkipAndNorm.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/SkipAndNorm.lean)).

The second half ties depth to travel. If each layer is one step of training
on the prompt, then the number of layers is the number of steps, and how well
the prompt can be fitted is set by the travel to its nearest fit. A prompt
whose examples lie along weak directions of the kernel needs more layers.
(**argued**)

## What is not shown

- **That trained transformers do this.** The proofs show a head *can* be one
  gradient step. That training finds such heads is reported for linear
  attention (**recalled**: von Oswald et al. 2023; Zhang, Frei and Bartlett
  2024) and is not shown here.
- **In-context learning with the softmax kept.** **open** here.
- **How fast the tokens merge.** Only that they cannot spread.
- **Everything else in a transformer.** Several heads, position signals, the
  feed-forward layers and normalisation are not modelled.
