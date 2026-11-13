# Counting: why a model can draw six fingers

**Proofs:** [`Convolution.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/Convolution.lean), [`Counting.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Counting.lean).

Notes from 14 Nov 2026. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/NewInputs/Counting.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Counting.lean) unless another file
is named), **argued**, **recalled** or **open**.

## The idea

Image models make a recognisable kind of mistake. A hand has six fingers. A
horse has five legs. A prompt asks for three cats and the picture has two.
These are all mistakes of number.

A count is a step. It is a whole number, and between `k` and `k + 1` there
is nothing. The models in this project are made of averages and of pieces
with limited slope. This note collects four facts that say a step is the
worst thing to ask of such a model.

## Between two counts there is a half

Take any read-out of an image that changes smoothly as the image changes.
Move the image along a path from one with `k` things to one with `k + 1`.
Somewhere on the path the read-out says `k + 1/2` (**proved**:
`exists_half_count`). This is the intermediate value theorem.

So a model that moves smoothly through the space of images cannot go from
five fingers to six without passing through images that are neither.

## The ideal denoiser blends counts

The ideal denoiser is an attention head over the training examples
(`averaging.md`). An attention head that scores two examples equally returns
the point half way between them (**proved**: `attend_two_of_const_score`).
So at a noisy input equally far from two training examples, the ideal
denoiser returns half of one and half of the other (**proved**:
`denoiser_two_of_equidistant`).

If one of those is a hand with five fingers and the other a hand with six,
the output is a blend of the two. An average of hands does not have a whole
number of fingers.

## Being sharp about a count costs slope

A model that says `k` at one input and `k + 1` at another has slope at least
one over the distance between them (**proved**:
`one_le_slope_mul_dist_of_count`). Two images that differ by one finger are
close. So telling them apart takes a steep model, and every result in this
project says slope has to be paid for.

## A local layer cannot see the whole picture

After `L` convolution layers an output depends only on the inputs within a
window (**proved**: `iterate_convolution_congr` in [`Convolution.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/Convolution.lean)). Two
images that agree inside the window get the same output there, however many
cats there are outside it. A count is a fact about the whole image.

## How this meets the squiggly line

Through **slope** and **averages**. The theorem says a line gets near the
data by being steep. A count is the limit of that: all step and no slope
anywhere else. An average cannot make a step, and a model of limited slope
can only round its corners.

## What is not shown

- **That this is why real models miscount.** The four facts show that
  counting is hard for a model built from averages and limited slope. They
  do not show that it is the cause of any real error. That is a question
  about trained networks, and it needs experiments. **open**
- **That all the mistakes are mistakes of number.** That is an observation
  about pictures. It is not a statement these proofs can reach.
- **That such a model cannot count at all.** It can, at a cost in slope and
  with layers that see the whole image. Newer models miscount less
  (**recalled**), which fits "expensive" better than "impossible".
- **Attention.** An attention layer does see the whole image. What it can
  count, and at what cost, is not analysed here.
