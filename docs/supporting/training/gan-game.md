# The GAN game: the best critic, and why the players spiral

**Proofs:** [`NetworkSlope.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean), [`SignedDistance.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/SignedDistance.lean), [`CrossEntropy.lean`](../../../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean), [`GanGame.lean`](../../../lean/SquigglyLine/Supporting/Training/GanGame.lean).

Notes from 14 Nov 2026. Written before the proofs, then updated once they
were done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/Training/GanGame.lean`](../../../lean/SquigglyLine/Supporting/Training/GanGame.lean) unless another file is
named), **argued**, **recalled** or **open**.

## The idea

A generative adversarial network is two players. The **maker** turns noise
into samples. The **critic** scores each sample: high for real, low for
made. The critic is trained to tell them apart, and the maker is trained to
fool it (**recalled**: Goodfellow et al. 2014).

Two facts about this game are classical. Both come out of things already in
this project.

## The critic's loss is a cross-entropy with a soft label

Look at one input. Say real data lands there with weight `p` and made data
with weight `q`. The critic's loss at that input is

    p * (loss for calling it real) + q * (loss for calling it made)

That is the cross-entropy of [`CrossEntropy.lean`](../../../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean), with total weight `p + q`
and the soft label `p / (p + q)` (**proved**: `criticLoss_eq_logLoss`). The
label is the share of what lands there that is real.

## Where real and made overlap, the best critic is finite

A cross-entropy with a soft label has a best score: the one whose prediction
equals the label. So where both `p` and `q` are positive, the best critic
predicts `p / (p + q)` (**proved**: `criticLoss_le_of_sigmoid_eq`,
`exists_best_critic`).

When the maker has won, `p = q` everywhere. The best critic then predicts
one half, which is the score zero (**proved**: `criticLoss_zero_le_of_eq`).
It can no longer tell.

## Where they do not overlap, the critic is asked to be steeper forever

Take an input where real data lands and made data does not: `q = 0`. The
label is one. A cross-entropy with a sure label has no best score: a larger
score always has a smaller loss (**proved**:
`strictAnti_criticLoss_of_no_fake`, from `strictAnti_logLoss_one` in
[`CrossEntropy.lean`](../../../lean/SquigglyLine/Supporting/Training/CrossEntropy.lean)).

Early in training the maker's samples are far from the data, so most inputs
are like this. The critic's scores are pushed up without limit on the real
side and down without limit on the made side. A critic that goes from very
low to very high across the gap between them is a steep one, and its slope
grows as long as it trains (**argued**).

That is the known trouble with the original game: a critic that is too good
gives the maker nothing to learn from (**recalled**: Arjovsky and Bottou
2017). The Wasserstein version answers it by holding the critic to slope
one. Then the gap it reports between a real sample and a made one is at most
their distance (**proved**: `sum_critic_gap_le` in [`NetworkSlope.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean)), and
a distance field is such a critic (**proved**:
`lipschitzWith_distanceField` in [`SignedDistance.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/SignedDistance.lean)).

## The two players spiral outward

The simplest game with two players: the maker holds a number `x`, the critic
holds a number `y`, and the payoff is `x * y`. The maker wants it small and
the critic wants it large. The only resting point is `x = y = 0`.

Let both take a gradient step at the same time, of size `η`. Then the
squared distance of `(x, y)` from the resting point is multiplied by exactly
`1 + η²` (**proved**: `sq_add_sq_gameStep`). After `n` steps it has grown by
`(1 + η²)^n` (**proved**: `sq_add_sq_iterate_gameStep`). Unless they start
at the resting point, they move away from it at every step (**proved**:
`sq_add_sq_lt_gameStep`).

So simultaneous gradient steps never settle this game, however small the
step. Each player's move is at right angles to the direction home.

## How this meets the squiggly line

Through **slope** and through **travel**.

The theorem says nearness is bought with slope. The original critic, on data
it can separate, is a loss that never stops asking for slope: there is no
finite best score. The Wasserstein critic is the same critic with its slope
capped at one, and what a slope-one function can report is a distance.

In every other note here, training travels to a fit and the travel is
finite. In this game the resting point is at distance zero and simultaneous
steps travel away from it. A game is not a descent.

## What is not shown

- **The whole game.** The best critic is found one input at a time. That
  the maker's loss against the best critic is a distance between the two
  distributions (the Jensen–Shannon divergence) is **recalled** and not in
  Lean.
- **That the slope really grows.** The scores are shown to have no finite
  best value where the data separates. That the critic's slope then grows is
  **argued**, as in `docs/supporting/training/cross-entropy.md`.
- **Real networks.** The spiral is for the payoff `x * y`. Near a resting
  point of a real game the same turning is present but mixed with other
  terms (**recalled**).
- **Fixes.** Alternating steps, looking ahead, and averaging the weights
  all change the factor `1 + η²`. None is analysed here. **open**
