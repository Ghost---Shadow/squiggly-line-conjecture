# 8. Folds

**In the repository:**
[`NarrowChain.lean`](../lean/SquigglyLine/Networks/NarrowChain.lean),
[`Depth.lean`](../lean/SquigglyLine/Networks/Depth.lean),
[`TentCloser.lean`](../lean/SquigglyLine/Networks/TentCloser.lean),
[`Bridge.lean`](../lean/SquigglyLine/Networks/Bridge.lean),
[`DepthSeparation.lean`](../lean/SquigglyLine/Supporting/NetworkShape/DepthSeparation.lean).
**You need:** chapters 4 and 7.

Part I was about curves. Part II is about networks. The first question is
the "parameters" claim of chapter 1: can a network buy squiggliness, and
with what?

## The idea

A ReLU neuron computes `max(value, 0)`. Its graph is flat and then
straight, with one corner. To draw a squiggly curve, a network has to
make many corners.

**One neuron per layer makes none that count.** A chain of single neurons,

```
relu(weight_1 × relu(weight_2 × relu(weight_3 × x + bias_3) + bias_2) + bias_1)
```

only ever rises, or only ever falls. Each layer does, and a chain of
such steps does too. It **never turns**, however deep it is.

**Two neurons per layer can fold.** This layer is called the tent:

```lean
noncomputable def APPLY_TENT
    (input : ℝ) : ℝ :=
  let first_neuron  := max input 0            -- ReLU: zero until the input passes 0
  let second_neuron := max (input - 1 / 2) 0  -- ReLU: zero until the input passes the fold at 1/2
  2 * first_neuron - 4 * second_neuron        -- slope 2 before the fold, and 2 - 4 = -2 after it
```

On the interval from 0 to 1 it goes up from 0 to 1 and back down to 0. It
folds the interval in half.

**Each new layer folds everything the earlier ones made.** Apply the tent
twice. At the inputs 0, 1/4, 1/2, 3/4 and 1 the output is 0, 1, 0, 1, 0.
Check one: the tent of 1/4 is 1/2, and the tent of 1/2 is 1. So two
layers draw four straight pieces. In general `layer_count` layers draw
`2 ^ layer_count` pieces with `2 × layer_count` neurons. The turns are
multiplied by depth and only added by width.

## Folding is squeezing

Each fold halves the reach of chapter 4. After `layer_count` folds every
label between 0 and 1 is hit within `1 / 2 ^ layer_count` of every input
(`iterate_tent_covers`). So by chapter 4 the curve is that close to every
point of the unit square:

```lean
theorem nearestDist_iterate_tent_le
    (layer_count : ℕ)
    (data_point : DataPoint ℝ)
    (input_in_unit : data_point.1 ∈ Set.Icc (0 : ℝ) 1)
    (label_in_unit : data_point.2 ∈ Set.Icc (0 : ℝ) 1) :
    let nearest_distance :=
      GET_NEAREST_DISTANCE (APPLY_TENT^[layer_count]) data_point
    let max_gap := 1 / 2 ^ layer_count  -- the gap found by `iterate_tent_covers`
    nearest_distance ≤ max_gap := by
```

`APPLY_TENT^[layer_count]` is the tent applied `layer_count` times: a
network that many layers deep. `Set.Icc 0 1` is the interval from 0 to 1.

So for this family the conjecture's chain "more layers, squigglier,
closer" holds, at an exponential rate. Ten layers pass within a
thousandth of every point. And by chapter 3 the price is slope: each fold
doubles it.

## Depth is the logarithm of frequency

There is an exact link between this network and the sine of chapter 6.
Look at the tent's output through the fixed lens `sin²(PI/2 × y)`. One
fold doubles the angle inside the sine (`sin_sq_tent`), so `layer_count`
folds give a single wave of frequency `2 ^ layer_count`
(`sin_sq_iterate_tent`). A fold is a frequency doubling.

## Width cannot keep up

A network with one hidden layer of ReLU neurons gets one corner per
neuron. To stay within one half of what `L + 1` tent layers draw, it
needs `2 ^ L` neurons (**proved** in
[`DepthSeparation.lean`](../lean/SquigglyLine/Supporting/NetworkShape/DepthSeparation.lean)).
Depth pays for squiggle exponentially better than width.

Width is still enough for gentle targets. A one-hidden-layer network
with `2n` neurons comes within `2 × slope / n` of any function on the
unit interval with that slope
([`UniversalApproximation.lean`](../lean/SquigglyLine/Supporting/NetworkShape/UniversalApproximation.lean)).
The cost in neurons goes as slope over error. Slope again.

## What is not shown

The weights of the tent are **chosen**. A network with **random** weights
is another matter. Measured: with random weights, more width does not
make the curve longer, and more depth makes it a little longer. Nothing
about random weights is proved here.

## Check yourself

1. What does the tent do to the input 0.3? And two tents in a row?
2. How many straight pieces do 5 tent layers draw, with how many
   neurons? How many neurons would one hidden layer need for the same
   number of pieces?
3. How many tent layers bring the curve within 0.01 of every point of
   the unit square?

**Answers.** (1) 0.6, and then 0.8. (2) 32 pieces with 10 neurons. One
hidden layer needs about 31, one per corner. (3) Seven, since `2 ^ 7` is
128.

Previous: [7. The theorem for any function](07-any-function.md) · Next: [9. Travel](09-travel.md)
