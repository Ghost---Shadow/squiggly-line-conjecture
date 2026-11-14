# 36. Attention

**In the repository:**
[`Attention.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Attention.lean),
[`AttentionRate.lean`](../lean/SquigglyLine/Supporting/NetworkShape/AttentionRate.lean),
note [`attention.md`](../docs/supporting/network-shape/attention.md).
**You need:** chapters 10, 11 and 15.

## The idea

If you have read how a transformer works, you have met the attention
head: every token asks a question, every token offers an answer, and the
head returns a blend of the answers. This chapter takes that blend
literally. It is a weighted average, and chapter 15 told you what an
average cannot do.

One head does three things for each query. It gives every token a
**score**. It turns the scores into **shares** with a softmax, so that
the shares are positive and add up to one. It returns the tokens' values
averaged with those shares. In the Lean file this is `ATTEND`, and in
Python it is `sum(softmax(score)[i] * value[i] for i in tokens)`.

> Attention never leaves the region its values span. Stacked alone, it
> pulls the tokens together at a rate set by the size of the scores. And
> without its softmax, one head is one step of gradient descent.

## An example you can do by hand

Three tokens carry the values 2, 4 and 9. Suppose the shares are 0.5,
0.25 and 0.25. The output is

```
0.5 × 2  +  0.25 × 4  +  0.25 × 9  =  1 + 1 + 2.25  =  4.25
```

Change the shares however you like, keeping them positive and adding to
one: the output stays between 2 and 9. With equal scores every share is a
third and the output is the plain average, 5.

Now stack layers. Say every score is at most `score_bound` = 0.5 in
size. One layer then keeps at most `1 − exp(−2 × 0.5)` of the spread,
which is `1 − 0.368 = 0.632`. The tokens start with range 9 − 2 = 7.
After one layer two tokens differ by at most `0.632 × 7`, about 4.4.
After ten layers they differ by at most `0.632^10 × 7`, about
`0.0101 × 7`, which is 0.07. With `score_bound` = 3 the factor is
`1 − exp(−6) = 0.9975`, and after 100 layers it is only about 0.78. Sharp
attention merges slowly.

Now the learning view. A model linear in its weights has two examples
with overlaps 1 and 2 with a new input, labels 3 and 1, and learning rate
0.1. One gradient step from zero weights predicts `0.1 × (1 × 3 + 2 × 1)`,
which is 0.5. Read the overlaps as scores and the labels as values: that
is an attention head with no softmax.

## The statement

First, the output of a head lies among its values.

```lean
/-- The output lies among the values. -/
theorem attend_mem_convexHull
    (score : Tokens → ℝ)
    (value : Tokens → Values) :
    let output := ATTEND score value
    let hull   := convexHull ℝ (Set.range value)
    output ∈ hull := by
```

*Read aloud:* whatever the scores are, the output is a blend of the
values.

The **convex hull** of some points is every blend of them. For numbers it
is the stretch from the smallest to the largest. The file also has `attend_mem_of_convex`, for any region with
no dents, and `iterate_attentionLayer_mem`: through any number of layers,
with any scores, tokens stay inside the region they started in.

Second, the rate, with its comment left out. The tokens here are numbers:
read them as one coordinate of the tokens.

```lean
theorem abs_iterate_attentionLayer_sub_le
    (score : TokenScorer Tokens ℝ)
    {score_bound : ℝ}
    (scores_are_bounded :
      ∀ any_tokens query token,
        |score any_tokens query token| ≤ score_bound)
    {tokens : Tokens → ℝ}
    {lower_bound upper_bound : ℝ}
    (tokens_above_lower : ∀ i, lower_bound ≤ tokens i)
    (tokens_below_upper : ∀ i, tokens i ≤ upper_bound)
    (layer_count : ℕ)
    (first_token second_token : Tokens) :
    let final_tokens  := (APPLY_ATTENTION_LAYER score)^[layer_count] tokens
    let disagreement  := |final_tokens first_token - final_tokens second_token|
    let shrink_factor := 1 - exp (-2 * score_bound)  -- one layer keeps this much of the spread
    let value_range   := upper_bound - lower_bound
    let shrunk_range  := shrink_factor ^ layer_count * value_range
    disagreement ≤ shrunk_range := by
```

*Read aloud:* after `layer_count` layers of attention alone, any two
tokens are at most `(1 − exp(−2 × score_bound))^layer_count` times their
starting range apart.

`APPLY_ATTENTION_LAYER` makes every token a query at once, with scores
that may depend on all the tokens. `f^[layer_count]` means applying `f`
that many times.

Third, attention as learning.

```lean
/-- **In-context learning.** Let the tokens be the examples. Score example `i`
by its overlap `predict query_features i` with the query, and let its value be
its label. Then one head of linear attention gives the prediction of one step
of gradient descent on those examples. -/
theorem prediction_one_step_eq_linearAttention
    (predict : Weights →L[ℝ] ExampleScores Examples)
    (labels : ExampleScores Examples)
    (learning_rate : ℝ)
    (query_features : Weights) :
    let prediction :=
      inner ℝ query_features
        (TAKE_GRADIENT_STEP predict labels learning_rate 0)
    let head_output :=
      learning_rate * ATTEND_LINEARLY (predict query_features) labels
    prediction = head_output := by
```

*Read aloud:* the prediction after one gradient step from zero weights is
the learning rate times a head that scores each example by its overlap
with the query and returns the labels.

`ATTEND_LINEARLY` is attention without the softmax: the sum of score times
value. `TAKE_GRADIENT_STEP` is the step of chapter 10, from weights `0`. A
second step does the same with each value replaced by the error still left
(`prediction_step_eq_linearAttention`).

## Why it is true

**An average stays inside.** The shares are positive and add to one
(`softmax_pos`, `sum_softmax`), and a region with no dents is closed under
such blends. For layers, induct on depth: one more layer is an average of
the tokens one layer earlier, which are inside by the step before.

**The merging rate** has four steps, which are the names after `have` in
the proof.

First, a floor on every share. If every score is at most `score_bound` in
size, then `exp(score)` lies between `exp(−score_bound)` and
`exp(score_bound)`. A share is `exp(score)` over the sum of all of them,
and that sum is at most `token_count × exp(score_bound)`. So every share
is at least `exp(−2 × score_bound) / token_count`
(`exp_neg_div_card_le_softmax`).

Second, two queries share that much. Two averages whose weights all sit
above a `floor` have `token_count × floor` of their weight in common, and
the common part cancels. What can differ is `1 − token_count × floor` of
the weights, times the range of the values
(`abs_sum_mul_sub_sum_mul_le`). With the floor from the first step,
`token_count × floor` is `exp(−2 × score_bound)`.

Third, one layer. The new tokens are answers to queries, so two of them
differ by at most `1 − exp(−2 × score_bound)` times the old range
(`abs_attend_sub_attend_le`).

Fourth, depth. Carry a band from the lowest to the highest token through
the layers. Each layer shrinks its width by the factor, so after
`layer_count` layers it is the factor to that power times the first range.
This is the one-factor rule of chapter 13 again.

**Attention as learning.** From zero weights, a gradient step adds
`learning_rate × transpose × labels` to the weights (chapter 10). Take the
inner product with the query's features: that is the overlap of each
example with the query, times its label (`inner_gradientStep_zero`). As a
sum over examples, it is `ATTEND_LINEARLY`.

## What it explains

**Why transformers need more than attention.** A transformer made of
attention alone is known to lose the differences between its tokens fast
(**recalled**: Dong, Cordonnier and Loukas 2021). The proof gives the rate
for a simple case: it depends only on how large the scores may be. The cure
sits in skip connections and feed-forward layers (chapter 31).

**In-context learning.** A stack of linear-attention heads can run one
gradient step per layer on the examples in its prompt, without changing
its own weights (**recalled**: von Oswald et al. 2023).

## How this meets the squiggly line

Through **averages** (chapter 15). An average is no steeper than what it
averages, so attention cannot supply the slope a line needs to pass near
its data. The squiggle has to come from other layers.

The second half uses the **kernel** (chapter 10): a token's score is the
overlap of its features with the query's. It also ties depth to **travel**
(chapter 9): if each layer is one step of training on the prompt, depth is
the number of steps. That reading is **argued**, not proved.

## What is not shown

- **That trained transformers do this.** The proofs show a head can be one
  gradient step, for a model linear in its weights and starting from zero.
- **In-context learning with the softmax kept.** **Open** here.
- **How fast tokens merge, for vector tokens and with skips.** The rate is
  proved for number-valued tokens and attention alone. A skip connection or
  a feed-forward layer can put the differences back, and that is not
  modelled.
- **A whole transformer.** Several heads and feed-forward layers are not
  modelled together with attention.

## Check yourself

1. Tokens carry the values 1 and 3. Can a head output 3.5?
2. Every score is at most 1 in size. By what factor does one layer shrink
   the spread of the tokens, at most? Give the formula and a number.
3. A model linear in its weights has one example with overlap 4 with a
   new input and label 2. The learning rate is 0.5. What does one gradient
   step from zero weights predict at the new input?

**Answers.** (1) No. By `attend_mem_convexHull` the output lies between 1
and 3. (2) The factor is `1 − exp(−2 × score_bound)`
(`abs_attend_sub_attend_le`), here `1 − exp(−2)`, about
`1 − 0.135 = 0.865`. (3) By `prediction_one_step_eq_linearAttention` it is
`0.5 × (4 × 2) = 4`.

Previous: [35. The landscape: connected fits and collapsed classes](35-the-landscape.md) · Next: [37. Ensembles and the ideal denoiser](37-ensembles-and-the-denoiser.md)
