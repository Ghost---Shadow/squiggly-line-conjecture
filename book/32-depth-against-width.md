# 32. Depth against width

**In the repository:**
[`DepthSeparation.lean`](../lean/SquigglyLine/Supporting/NetworkShape/DepthSeparation.lean),
[`UniversalApproximation.lean`](../lean/SquigglyLine/Supporting/NetworkShape/UniversalApproximation.lean),
[`KolmogorovArnold.lean`](../lean/SquigglyLine/Supporting/NetworkShape/KolmogorovArnold.lean),
notes [`depth-separation.md`](../docs/supporting/network-shape/depth-separation.md) and
[`universal-approximation.md`](../docs/supporting/network-shape/universal-approximation.md).
**You need:** chapters 3, 7 and 8.

## The idea

"A network with one hidden layer can approximate any continuous
function." This is the universal approximation theorem (**recalled**:
Cybenko 1989; Hornik 1991; Leshno et al. 1993), and it is often quoted as
"a network can learn anything". It says less. It says a good network
exists. It does not say how big it is, or that training finds it.

This chapter puts a price on it, from two sides. From above: a ReLU
network with one hidden layer follows a function of slope at most
`slope_limit` to within `tolerance` with about `slope_limit / tolerance`
units. From below: a function with many turns costs one unit per turn
when the network is wide and shallow, and only a few neurons when it is
deep (**recalled**: Telgarsky 2016, "Benefits of depth in neural
networks"). Chapter 8 met the second result. Here you see both together,
and a third result that follows from the first.

> Wide and shallow pays one unit per turn. Deep pays one layer per
> doubling of turns. One hidden layer pays slope over error to follow
> any gentle function.

## An example you can do by hand

**Depth.** The tent layer of chapter 8 is `2 × relu(input) − 4 × relu(input −
1/2)`: two neurons. It sends `input` to `2 × input` up to one half and to `2 − 2 × input`
after. Stack three of them. At `1/8` the first gives `1/4`, the second
`1/2`, the third `1`. At `2/8` the values are `1/2`, `1`, `0`. On the
nine grid points `0, 1/8, ..., 1` the stack gives `0, 1, 0, 1, 0, 1, 0,
1, 0`. That is four peaks from six neurons. Ten tent layers use 20
neurons and make 512 peaks.

**Width.** A one-hidden-layer network follows those four peaks only if
it has at least four units: the theorem below says `2 ^ 2`, which is 4.
For ten tent layers it says at least `2 ^ 9`, which is 512 units, against
20.

**The price of a slope.** Let `model` have slope at most 2. Cut the
interval from 0 to 1 into `piece_count` pieces. The network of this
chapter has `2 × piece_count` units and is within
`2 × 2 / piece_count` of `model`. For a tolerance of 0.1 you need
`4 / piece_count ≤ 0.1`, so 40 pieces, so 80 units.

## The statement

The cost of wide and shallow, from below.

```lean
/-- **Depth separation.** `layer_count + 1` tent layers use
`2 (layer_count + 1)` neurons. A network with one hidden layer that stays
within one half of them at the `2 ^ (layer_count + 1) + 1` grid points has at
least `2 ^ layer_count` units. -/
theorem depth_separation
    (units : Finset Index)
    (unit_gain : Index → ℝ)
    (unit_slope : Index → ℝ)
    (unit_bias : Index → ℝ)
    (layer_count : ℕ)
    (follows_zigzag : ∀ grid_index : ℕ, grid_index ≤ 2 ^ (layer_count + 1) →
      |EVALUATE_SHALLOW_NETWORK units unit_gain unit_slope unit_bias
          ((grid_index : ℝ) / 2 ^ (layer_count + 1))
        - APPLY_TENT^[layer_count + 1]
          ((grid_index : ℝ) / 2 ^ (layer_count + 1))|
        < 1 / 2) :
    let units_needed := 2 ^ layer_count  -- one unit per turn; the zigzag has 2 ^ layer_count turns
    let unit_count := units.card
    units_needed ≤ unit_count := by
```

*Read aloud:* if a one-hidden-layer ReLU network stays within one half of
the stacked tents at every grid point, then it has at least
`2 ^ layer_count` units.

`EVALUATE_SHALLOW_NETWORK` is the Python `sum(gain[j] × max(slope[j] ×
input + bias[j], 0) for j in units)`: a sum of ReLU units. `Finset Index`
is the set of unit names, and `units.card` is how many there are.
`APPLY_TENT^[layer_count + 1]` is the tent layer applied `layer_count +
1` times. The network has to be within one half only at the grid points,
which is a weak demand: below one half where the stack is 0, above where
it is 1.

The cost from above.

```lean
/-- **A network of `2 * piece_count` units is within
`2 * slope_limit / piece_count` of `model`.** -/
theorem relu_network_close
    (slope_is_bounded :
      ∀ input other_input,
        |model input - model other_input|
          ≤ slope_limit * |input - other_input|)
    (piece_count_pos : (0 : ℝ) < piece_count)
    {input : ℝ}
    (input_nonneg : 0 ≤ input)
    (input_le_one : input ≤ 1) :
    let approximation_error :=
      |INTERPOLATE_WITH_RELU model piece_count piece_count input - model input|
    let error_bound := 2 * slope_limit / piece_count  -- from `reluInterp_spec`
    approximation_error ≤ error_bound := by
```

*Read aloud:* on the interval from 0 to 1, a function of slope at most
`slope_limit` is within `2 × slope_limit / piece_count` of the ReLU
network with `2 × piece_count` units that follows it piece by piece.

`INTERPOLATE_WITH_RELU model piece_count piece_count` is that network.
From it, `universal_approximation` says that for any `tolerance > 0` some
number of pieces is enough. And `abs_kanNode_sub_le` says the same for a
node that adds one learnable curve per input: its ReLU version is within
`2 × (sum of the slope limits) / piece_count` of it. The statement is a
sum over the inputs, so it needs the sum of the slope limits of the
curves.

## Why it is true

**Below.** A ReLU unit is flat on one side of a point, its kink, and a
straight slope on the other (`affineOn_reluUnit`). So on any stretch with
no kink in it, every unit is a straight line, and so is their sum. A
straight line cannot be lower at both ends of a stretch than in the
middle (`not_zigzag`). So a stretch where the network goes up and then
down holds the kink of some unit (`exists_kink_of_zigzag`). A zigzag with
`turn_count` ups and downs has that many stretches that do not overlap,
and a unit has one kink. So each needs a different unit
(`card_ge_of_zigzag`). The stacked tent has `2 ^ layer_count` turns on
the grid, and the network is allowed an error of one half, so it must go
up and down at each (`depth_separation`).

**Above.** A ramp is flat, then rises across one piece, then is flat at
full height. It is two ReLU units: one switches the rise on, one switches
it off (`EVALUATE_RAMP`). Scale each ramp to match the rise of `model`
across its piece and add them. Before a piece, its ramp adds nothing.
After it, its ramp adds the full rise, so the network sits exactly on
`model` at the end of each piece. Inside a piece the network runs
straight between two values of `model`, and `model` cannot stray far
from either end, because its slope is at most `slope_limit`. Going
piece by piece along the interval gives the bound `reluInterp_spec`.

## What it explains

That the universal approximation theorem is true and is not the comfort it
sounds like. The proof here is for one input, and it gives the size: the
number of units goes as `slope_limit / tolerance`. This is chapter 3
again. A squigglier target is a steeper one, and a steeper one costs
units in proportion.

That depth is worth having. A wide and shallow network pays one unit per
turn. A deep one doubles the turns at every layer. The result is for a
chosen target, the stacked tent, so it says depth can be exponentially
cheaper for some functions. It does not say real data needs it
(**open**).

That a learnable curve on an edge of a Kolmogorov–Arnold network is a few
folds. How many is set by total slope over the error allowed, as
everywhere in this chapter.

## How this meets the squiggly line

Through **slope** (chapter 3) and **folds** (chapter 8). A fold is how a
layer buys a turn. Squiggliness is what parameters buy, and this chapter
says how the price depends on where they are put: in width, one turn per
unit; in depth, double the turns per layer. By the theorem of chapter 7 a
squigglier line starts closer to the data.

## What is not shown

- **Two hidden layers against three.** The depth result compares one
  hidden layer with many (**open**).
- **Functions that matter.** The stacked tent is a made-up target.
  Whether real data needs this many turns is not addressed (**open**).
- **Functions that are only continuous.** The approximation proof is for
  bounded slope. A continuous function on a closed interval can be handled
  with a little more care (**recalled**), and that is not done here.
- **More than one input.** The construction is for one input. In many
  dimensions the count of pieces grows very fast (**recalled**).
- **Training.** That a network exists does not mean gradient descent finds
  it (**open**).
- **Other activations.** The counting uses the fact that a ReLU unit has
  one kink.

## Check yourself

1. Five tent layers are stacked. How many neurons are there? What is the
   fewest units a one-hidden-layer network can have if it stays within
   one half of the stack at the grid points?
2. A function on the interval from 0 to 1 has slope at most 3. How many
   units does `relu_network_close` use to get within 0.1, and why?
3. A Kolmogorov–Arnold node has three edge curves with slope limits 1, 2
   and 3. With `piece_count` equal to 100, how far can its ReLU version be
   from it?

**Answers.** (1) Ten neurons. Here `layer_count + 1` is 5, so
`layer_count` is 4, and by `depth_separation` at least `2 ^ 4 = 16`
units. (2) The error bound is `2 × 3 / piece_count = 6 / piece_count`.
For this to be at most 0.1 you need `piece_count` of at least 60, which
means `2 × 60 = 120` units. (3) At most `2 × (1 + 2 + 3) / 100 = 0.12`, by
`abs_kanNode_sub_le`.

Previous: [31. Skips and normalisation](31-skips-and-normalisation.md) · Next: [33. Convolution](33-convolution.md)
