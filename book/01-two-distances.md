# 1. Two distances

**In the repository:**
[`Defs.lean`](../lean/SquigglyLine/Theorem/Defs.lean),
[`Conjecture.lean`](../lean/SquigglyLine/Theorem/Conjecture.lean).
**You need:** nothing.

## The picture

Scatter some points on a sheet of paper. Without looking at them, draw two
curves from left to right: one smooth, one squiggly. The squiggly one
passes closer to the points, because it visits more of the paper.

A neural network computes a function, and the graph of that function is
such a curve. The points are the training data. So here is an idea about
why big networks learn fast:

> A network with more parameters draws a squigglier curve before training.
> So it starts closer to its data. So it learns faster.

This was the squiggly line conjecture. It is three claims in a chain, and
this book is about what happens to each of them.

## Two ways to be close

"Closer to the data" can mean two different things.

![Sixteen points beside a smooth curve and a squiggly curve, with the two distances drawn.](../graphs/readme_two_distances.png)

- The **nearest distance** is the distance from a data point to the nearest
  point of the curve, in any direction. This is what your eye sees.
- The **vertical error** is the distance straight up or down from the data
  point to the curve. This is what training measures: the label minus the
  prediction.

**An example.** The model is the straight line `y = 3x`. The data point is
`(0, 1)`. Straight down from the point, the line is at height 0, so the
vertical error is 1. But the line is steep, and it passes much closer than
that off to the side: the nearest distance is `1 / √10`, about 0.32.

The whole theorem lives in the gap between these two numbers.

## The words the proofs use

The Lean files give each of these things a name. You will see them in
every chapter.

| Name | Meaning | In Python |
|---|---|---|
| `Model Inputs` | a function from inputs to real numbers | `Callable[[Input], float]` |
| `DataPoint Inputs` | a pair `(input, label)` | `tuple[Input, float]` |
| `GET_INPUT`, `GET_LABEL` | the two parts of a data point | `data_point[0]`, `data_point[1]` |
| `GET_GRAPH` | the squiggly line: every `(input, model(input))` | |
| `GET_NEAREST_DISTANCE` | distance from a data point to the line | |
| `GET_VERTICAL_ERROR` | `abs(label - model(input))` | |
| `GET_RESIDUAL_LOSS` | any loss that reads only `label - model(input)` | |

The names in capitals are functions and constants. Functions are verbs:
`GET_NEAREST_DISTANCE model data_point` returns a number.

## The conjecture, as three claims

| # | Claim | What happens to it |
|---|---|---|
| 1 | **Geometry.** A squigglier curve has a smaller nearest distance. | True. Chapters 4, 6 and 7. |
| 2 | **Parameters.** More parameters give a squigglier curve. | Mixed. True for depth, chapter 8. Open for random weights, chapter 47. |
| 3 | **Learning.** A smaller nearest distance means a smaller loss at the start. | False. Chapter 5. |

So the picture is right and the conclusion is wrong. The nearness is real,
but the loss cannot see it. What the nearness does buy is a short distance
to move, and chapter 9 measures that distance.

## Check yourself

1. The model is the flat line `y = 0` and the data point is `(2, 5)`. What
   are the two distances?
2. Can the nearest distance be larger than the vertical error?
3. Which of the two does a regression loss measure?

**Answers.** (1) Both are 5: the nearest point of a flat line is straight
below. (2) No. Straight up or down is one way to reach the curve, so the
nearest way is no longer. Chapter 3 proves it. (3) The vertical error.

Previous: [Preface](00-preface.md) · Next: [2. How to read a proof here](02-reading-a-proof.md)
