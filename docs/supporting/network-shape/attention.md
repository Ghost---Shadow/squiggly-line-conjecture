# Attention: a weighted average, and one step of training

**Proofs:** [`Depth.lean`](../../../lean/SquigglyLine/Networks/Depth.lean), [`MarkovChains.lean`](../../../lean/SquigglyLine/Networks/MarkovChains.lean), [`Attention.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/Attention.lean), [`AttentionRate.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/AttentionRate.lean), [`HardChoices.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/HardChoices.lean), [`SkipAndNorm.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/SkipAndNorm.lean), [`CrossEntropy.lean`](../../../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean).

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

## How fast the tokens merge

Notes from 13 Nov 2026. Proofs in
[`lean/SquigglyLine/Supporting/NetworkShape/AttentionRate.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/AttentionRate.lean). The tokens
here are numbers: read them as one coordinate of the tokens, or as any one
read-out of them.

"Cannot spread" has a rate when the scores are bounded.

- **Every token gets a share.** If every score is at most `B` in size, every
  share of the softmax is at least `exp(-2B) / n`, for `n` tokens
  (**proved**: `exp_neg_div_card_le_softmax`).
- **Two queries agree on that much.** Two averages whose weights all sit
  above a floor `m` differ by at most `1 - n * m` times the range of the
  values (**proved**: `abs_sum_mul_sub_sum_mul_le`). The floor is the part of
  the two averages that is the same.
- **One layer shrinks the spread.** With the floor `exp(-2B) / n`, two
  queries give answers that differ by at most `1 - exp(-2B)` times the range
  of the values (**proved**: `abs_attend_sub_attend_le`).
- **Depth merges at a geometric rate.** After `L` layers of attention alone,
  any two tokens differ by at most `(1 - exp(-2B))^L` times the range they
  started in (**proved**: `abs_iterate_attentionLayer_sub_le`).

So attention alone loses the differences between its tokens geometrically
in depth. The rate depends only on how large the scores are allowed to be.
Sharp attention (large scores) merges slowly; flat attention merges at once.

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

## Hard choices: straight-through, a cold softmax, Hopfield recall

Notes from 14 Nov 2026. Proofs in
[`lean/SquigglyLine/Supporting/NetworkShape/HardChoices.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/HardChoices.lean).

Some layers have to pick: round a number, or take the top score. A pick is
a step, and a step is the limit of a squiggle: all its slope is at the jump.

- **A hard step sends no gradient back.** Away from its jump the step
  function has slope zero (**proved**: `hasDerivAt_step_of_pos`). Training
  by gradient cannot see through it.
- **The straight-through trick.** Write
  `(hard - soft).detach() + soft`, where `soft` is a gentle stand-in for the
  hard step and `detach` means "treat as a fixed number". Forward, this is
  the hard step (**proved**: `straightThrough_self`). Backward, it has the
  slope of the stand-in (**proved**: `hasDerivAt_straightThrough`). The
  value of a step is kept and the slope of a line is borrowed.
- **A cold softmax picks.** A softmax at temperature `τ` is the usual
  stand-in for taking the top score. If the top score leads the rest by
  `gap`, its share is within `(n - 1) * exp(-gap / τ)` of one (**proved**:
  `one_sub_softmax_div_le`). So as `τ` falls the softmax tends to the pick
  itself. Dividing the scores by `τ` multiplies their slope by `1 / τ`
  (`network-slope.md`), so the nearer to a pick, the steeper. That is the
  trade in Gumbel-softmax. The Gumbel noise, which makes the pick a random
  draw from the softmax, is not shown.
- **Hopfield recall.** A modern Hopfield network stores patterns and
  updates its state to an attention-weighted average of them, scored by
  overlap with the state. For patterns and a state of length one that
  update is the ideal denoiser of `averaging.md` (**proved**:
  `hopfield_eq_denoiser`). Recall is denoising: the state moves toward the
  stored patterns nearest to it and never leaves the region they span. The
  classic network of 1982, with its energy that only falls, is not shown.

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
- **How fast the tokens merge, for vector tokens and with skips.** The rate
  is proved for number-valued tokens and attention alone. A skip connection
  or a feed-forward layer can put the differences back, and that is not
  modelled.
- **A whole transformer.** Several heads and the feed-forward layers are not
  modelled together with attention. The parts are in other notes: position
  signals in `docs/networks/position-embeddings.md`, normalisation in
  `docs/supporting/training/symmetry.md`, and skips in `skip-and-norm.md`.
