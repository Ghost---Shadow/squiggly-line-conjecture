# Depth separation: what a wide, shallow network cannot do cheaply

**Proofs:** [`Depth.lean`](../../../lean/SquigglyLine/Networks/Depth.lean), [`DepthSeparation.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/DepthSeparation.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/NetworkShape/DepthSeparation.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/DepthSeparation.lean) unless another file is named),
**recalled**, or **open**.

## The idea

The wind tunnel notes say depth multiplies the turns: each layer folds
everything the earlier layers made. A stack of `L` tent layers, two neurons
each, draws a zigzag that goes up and down `2^(L−1)` times
(**proved** earlier: `iterate_tent_dyadic` in [`Depth.lean`](../../../lean/SquigglyLine/Networks/Depth.lean)).

Could a network with one hidden layer do the same with about as many neurons?
No. This is a known result (**recalled**: Telgarsky 2016, "Benefits of depth
in neural networks"). The argument is short enough to check by machine, and it
uses nothing but counting.

## The argument

**A ReLU unit bends once.** One unit is flat on one side of a point and a
straight slope on the other. Call that point its kink. On any stretch of
inputs that does not contain its kink, the unit is a straight line
(**proved**: `affineOn_reluUnit`).

**So a one-layer network is straight between kinks.** A network with one
hidden layer adds up its units. On a stretch that contains no unit's kink,
every unit is a straight line, so the sum is a straight line.

**A straight line cannot go up and come back down.** If a function is lower at
both ends of a stretch than at a point in the middle, it is not a straight
line there (**proved**: `AffineOn.not_zigzag`). So that stretch holds a kink
of some unit (**proved**: `exists_kink_of_zigzag`).

**Each up-and-down needs its own unit.** Take a zigzag that goes up and down
`m` times. The `m` stretches do not overlap, and a unit has only one kink. So
each stretch needs a different unit, and the network has at least `m` units
(**proved**: `card_ge_of_zigzag`).

## The result

Put the two sides together.

> A stack of `L + 1` tent layers has `2(L + 1)` neurons. Any network with one
> hidden layer that stays within one half of it at the grid points needs at
> least `2^L` neurons.

(**proved**: `depth_separation`.) Ten tent layers use 20 neurons. A one-layer
network needs at least 512 just to get within a half of the same zigzag.

The one-layer network does not have to match the stack. It only has to be
below one half where the stack is 0 and above one half where the stack is 1.
Even that much costs a neuron per turn.

## How this meets the squiggly line

Squiggliness is what parameters buy. This result says how the price depends on
where the parameters are put. In depth, each added layer doubles the turns.
In width, each added neuron adds one. So the same number of parameters makes a
much squigglier line when it is spent on depth, and by the theorem a
squigglier line starts closer to the data.

## What is not shown

- **Two hidden layers against three.** The result compares one hidden layer
  with many. **open**
- **Functions that matter.** The stacked tent is a made-up target. Whether
  real data needs this many turns is not addressed. **open**
- **Training.** That a deep network can draw the zigzag does not mean
  gradient descent finds it. **open**
- **Other activations.** The counting uses the fact that a ReLU unit has one
  kink.
