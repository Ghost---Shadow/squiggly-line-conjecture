# 15. Averages

**In the repository:**
[`Attention.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Attention.lean),
[`AttentionRate.lean`](../lean/SquigglyLine/Supporting/NetworkShape/AttentionRate.lean),
[`Averaging.lean`](../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean),
[`Counting.lean`](../lean/SquigglyLine/Supporting/NewInputs/Counting.lean),
[`Temperature.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Temperature.lean),
[`Neighbours.lean`](../lean/SquigglyLine/Supporting/NewInputs/Neighbours.lean).
**You need:** chapters 10, 11 and 14.
**The proofs, one by one:** part VI, chapters 36 to 41.

## The idea

A great deal of modern deep learning is built from weighted averages:
attention, ensembles, diffusion models, nearest neighbours. An average
has one plain property.

> An average never leaves the region its inputs span.

The average of 2, 4 and 9 lies between 2 and 9, whatever the weights.
This chapter is that one property, used five times.

## Attention is an average

An attention head scores each token, turns the scores into shares that
add up to one, and returns that blend of the tokens' values. So its
output is a weighted average, and any stack of such heads keeps every
token inside the region the tokens started in.

Stacked alone, attention also pulls the tokens together. If the scores
are at most `score_bound` in size, each layer shrinks the spread of the
tokens by a fixed factor below one, so `depth` layers shrink it by that
factor to the power `depth` (`abs_iterate_attentionLayer_sub_le`). This
is the one-factor rule of chapter 13, and the reason transformers need
their skip connections.

## Attention is one step of training

Take a model that is linear in its weights, starting from zero. Give it
some examples and one step of gradient descent. By the kernel trick of
chapter 11, its prediction at a new input is

```
learning_rate × Σ kernel(example, new input) × label of the example
```

Read that as an attention head. The tokens are the examples. The score
of a token is its overlap with the query. Its value is its label. Leave
out the softmax. Then the head's output is that prediction
(`prediction_one_step_eq_linearAttention`).

So a stack of such heads can run gradient descent on the examples in
its prompt, one step per layer, without changing its own weights. This
is the simplest account of in-context learning. With the softmax kept,
the question is open here.

## The ideal denoiser is an average of the training set

A diffusion model learns to remove noise. The best possible denoiser has
a closed form: it is an attention head over the training examples, with
nearer examples scored higher
([`Averaging.lean`](../lean/SquigglyLine/Supporting/NewInputs/Averaging.lean)).
So it never leaves the region the training examples span.

## A count is the worst thing to ask of an average

A count is a whole number, and it jumps. Averages and limited slopes do
not jump. [`Counting.lean`](../lean/SquigglyLine/Supporting/NewInputs/Counting.lean)
has three short facts.

- A read-out that changes smoothly from `count` to `count + 1` says
  `count + 1/2` somewhere on the way (`exists_half_count`).
- At a noisy input equally far from two training examples, the ideal
  denoiser returns the point half way between them
  (`denoiser_two_of_equidistant`). If one is a hand with five fingers and
  the other a hand with six, the answer is a blend of the two.
- Telling `count` from `count + 1` takes slope at least one over the
  distance between the inputs (`one_le_slope_mul_dist_of_count`, the
  statement you read in chapter 2).

These show that counting is hard for a model made of averages and
limited slope. They do not show that this is why a real image model
draws six fingers. That needs experiments.

## More averages

- **Ensembles.** The squared error of an average of models is the
  average of their errors minus the spread between them. So an ensemble
  is never worse than its members are on average, and it gains exactly
  what they disagree by.
- **Temperature.** Sample from a softmax of scores divided by a
  temperature. As the temperature falls, the average score of a sample
  never falls (`expectedScore_softmax_mono`), and the samples
  concentrate on the top score (`one_sub_softmax_div_le`). One dial moves
  quality up and variety down.
- **Nearest neighbours.** Copying the label of the nearest training input
  is wrong by at most the slope of the truth times the distance to that
  input. Nearness times slope again.

## What is not shown

- In-context learning with the softmax kept.
- Any measure of variety that falls at every step as the temperature
  falls. Only the two ends are proved.
- That real attention layers, with their skips and other layers between
  them, merge tokens. The rate is for attention alone.

## Check yourself

1. An attention head sees values 2, 4 and 9. Can it output 10?
2. An attention head gives two examples the same score. Their values are
   5 and 6. What does it return?
3. Why can an average of gentle models not draw a sharp step?

**Answers.** (1) No. A weighted average stays between 2 and 9. (2) 5.5
(`attend_two_of_const_score`). (3) An average is no steeper than its
steepest member (chapter 14), and a sharp step needs a large slope.

Previous: [14. Three ways to combine slope](14-combining-slope.md) · Next: [16. New inputs](16-new-inputs.md)
