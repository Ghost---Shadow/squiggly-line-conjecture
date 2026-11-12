# The squiggly line theorem, without the sines

Notes from 11 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in `lean/SquigglyLine/Theorem/Compression.lean` and
`lean/SquigglyLine/Networks/TentCloser.lean`) or **open**.

## Why the title was loaded

The theorem so far is about one family, the sine, with one input. Every
summary of it has to add "for sines" and "a conjecture for networks". Two more
proofs remove most of that.

## What "squigglier" means, for any function

Take any function at all, of any number of inputs. Squeeze it sideways by a
factor `w`: the new function at `x` is the old function at `w·x`. Every wiggle
is now `w` times narrower. That is what "squigglier" means, with nothing about
sines in it. A sine of frequency `w` is the plain sine squeezed by `w`.

## The theorem for any function

Squeezing a function by `w` does three things, and each is exact.

1. **Closer.** If the function reached every label within a distance `ρ` of
   every input, the squeezed one reaches every label within `ρ / w`. So its
   nearest-point distance to any data point is at most `ρ / w`
   (**proved**: `CoversWithin.compress`).
2. **Steeper.** If the function had slope at most `K`, the squeezed one has
   slope at most `w·K`. So its nearest-point distance is at least the vertical
   error divided by `√(1 + (w·K)²)` (**proved**: `lipschitzWith_compress`).
3. **No better at the start.** Take a random function whose output has the
   same distribution at every input. Squeezing it does not change that
   distribution, so it does not change the expected loss, for any regression
   loss (**proved**: `marginal_compress_eq`).

And, as before, the nearness is a distance to move: a warp of the input that
moves no point by more than `ρ / w` fits any target (**proved**). The four
parts together are `squiggly_line_theorem_general`.

Nothing here needs one input, or a sine, or a period. The sine theorem is the
special case where the function is a sine with a random phase.

## A network for which the conjecture is true

The ReLU side has a family where "more parameters, closer" holds outright.

Take the fold from `Depth.lean`: one layer with two neurons that folds the
interval from 0 to 1 in half. Stack `L` of them. The network has `2L` neurons.

> For every point of the unit square, the curve drawn by this network passes
> within `1 / 2^L` of it.

(**proved**: `nearestDist_iterate_tent_le`.) Each layer halves the distance. Ten layers bring the curve
within a thousandth of every point of the square.

So for this family the first two claims of the original conjecture are true,
and with an exponential rate: more layers, squigglier, closer. The third claim
still fails for the same reason as always. The network is also `2^L` times
steeper, and its vertical error at a given point is no smaller.

## What this does to the title

With these two results the statement no longer depends on the sine:

> **Closer, steeper, and no better at the start.** Squeezing any function by
> `w` brings it `w` times closer to the data and makes it `w` times steeper,
> and leaves its expected loss unchanged.

And "a conjecture for neural networks" becomes narrower and more exact:

> True for a constructed family of ReLU networks. Open for networks with
> random weights.

## What stays open

- **Random weights.** The fold network has chosen weights. Whether a network
  with random weights gets closer as it grows is the original question, and it
  is still **open**. The evidence in this repository says no for width.
- **Training.** That a small warp exists is proved. That training finds it is
  **open**.
