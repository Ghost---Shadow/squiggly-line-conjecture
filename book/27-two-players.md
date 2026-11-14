# 27. Two players: the GAN game

**In the repository:**
[`GanGame.lean`](../lean/SquigglyLine/Supporting/Training/GanGame.lean),
note [`gan-game.md`](../docs/supporting/training/gan-game.md).
**You need:** chapters 3, 4 and 13.

## The idea

A **generative adversarial network** is two players (**recalled**:
Goodfellow et al. 2014). The **maker** turns noise into samples. The
**critic** scores each sample: high for real, low for made. The critic is
trained to tell them apart. The maker is trained to fool it.

Everything so far in Part IV was one player going downhill. Here there
are two, and each one's gain is the other's loss. Two facts about this
game are classical, and both come out of things already in this book.

> At each input the critic's loss is a cross-entropy with a soft label,
> so where real and made data overlap the best critic is finite. And
> in the simplest game, two players stepping together move away from
> rest by the factor `1 + learning_rate²` per step.

## An example you can do by hand

**The critic.** At one input, real data lands with weight 3 and made data
with weight 1. The share that is real is `3 / (3 + 1) = 0.75`. The best
critic predicts 0.75 there. If both weights are 2, the share is 0.5, and
the best critic predicts one half: it cannot tell.

If made data does not land there at all, the share is 1. A prediction
can come closer to 1 for ever, but never reach it.

**The spiral.** The maker holds a number `x`, the critic holds a number
`y`, and the payoff is `x × y`. The maker wants it small and the critic
wants it large. Start at `(1, 0)` with `learning_rate = 0.1`. Each player
steps at the same time:

```
new x = x − learning_rate × y        new y = y + learning_rate × x
(1, 0)  →  (1, 0.1)  →  (0.99, 0.2)
```

The squared distance from rest, `x² + y²`, goes `1`, then `1.01`, then
`0.9801 + 0.04 = 1.0201`. Each is `1.01` times the one before. It grows
every step, though both players are walking downhill by their own
measure.

## The statement

The first fact is `criticLoss_eq_logLoss`: the critic's loss at an input
is the total weight times the cross-entropy (`GET_LOG_LOSS`, chapter 25)
against the label "share that is real". A **score** becomes a prediction
through the sigmoid, which squeezes it between 0 and 1.

```lean
/-- **Where made data is absent, no score is best.** A larger score always has a
smaller loss, so the critic is asked to be steeper forever. -/
theorem strictAnti_criticLoss_of_no_fake
    {real_weight : ℝ}
    (real_pos : 0 < real_weight) :
    let loss_without_made := GET_CRITIC_LOSS real_weight 0
    StrictAnti loss_without_made := by
```

*Read aloud:* where only real data lands, a higher score always has a
lower loss.

`StrictAnti` means "strictly going down as the input goes up".

```lean
/-- **The players spiral outward.** After `step_count` simultaneous steps the
squared distance from the resting point has grown by `(1 + learning_rate²) ^
step_count`. -/
theorem sq_add_sq_iterate_gameStep
    (learning_rate : ℝ)
    (state : PlayerNumbers)
    (step_count : ℕ) :
    let stepped         := (TAKE_GAME_STEP learning_rate)^[step_count] state
    let distance_after  := stepped.1 ^ 2 + stepped.2 ^ 2
    let distance_before := state.1 ^ 2 + state.2 ^ 2
    let growth          := (1 + learning_rate ^ 2) ^ step_count  -- `1 + learning_rate²` per step
    distance_after = growth * distance_before := by
```

*Read aloud:* after any number of steps, the squared distance from rest
is the starting one times `(1 + learning_rate²)` to the power of that
number.

`TAKE_GAME_STEP` is one simultaneous step, as in the example, and
`^[step_count]` means "do it `step_count` times". The one-step case is
`sq_add_sq_gameStep`.

Two more results. Where real and made weights are both positive, the best
critic predicts the real share (`criticLoss_le_of_sigmoid_eq`,
`exists_best_critic`). When the weights are equal, the score zero is best
(`criticLoss_zero_le_of_eq`). And `sq_add_sq_lt_gameStep` says that off
the resting point, with a nonzero step, every step moves the players
further from it.

## Why it is true

**The soft label.** At one input the loss is `real_weight` times the cost
of calling it real, plus `made_weight` times the cost of calling it made.
Take out the total weight as a factor. What is left is a cross-entropy
whose label is the real share. The proof is a line of algebra.

**A finite best, or none.** A cross-entropy with a soft label has a best
score: the one whose prediction equals the label. With a sure label, a
larger score always has a smaller loss (`strictAnti_logLoss_one`), and
with no made data the critic's loss is the real weight times that. So no
score is best.

**The spiral.** Write the step as `(x − learning_rate × y, y +
learning_rate × x)`. Square both parts and add. The cross terms cancel,
and what is left is `(1 + learning_rate²) × (x² + y²)`. Each player's
move is at right angles to the direction home, as in Pythagoras. The
many-step version repeats this, and the proof is an induction on the
number of steps.

## What it explains

**A critic that is too good.** Early in training the maker's samples are
far from the data, so most inputs are like the one with no made data. The
critic's scores are pushed up without limit on the real side and down
without limit on the made side. A critic that goes from very low to very
high across the gap between them is steep. That its slope really grows as
it trains is **argued**, not proved. A critic that is too good gives the
maker nothing to learn from (**recalled**: Arjovsky and Bottou 2017).

**The Wasserstein critic.** The remedy holds the critic to slope one.
Then the gap it reports between a real sample and a made one is at most
their distance (`sum_critic_gap_le`), and a distance field is such a
critic (`lipschitzWith_distanceField`). This is the slope sandwich of
chapter 3 at work: a critic of slope one can report a distance and no
more.

## How this meets the squiggly line

Through **slope** and through **travel**. The theorem says nearness is
bought with slope (chapter 3). The original critic, on data it can
separate, has a loss that never stops asking for slope, because there is
no finite best score. The Wasserstein critic is the same critic with its
slope capped at one.

In every other chapter of Part IV, training travels to a fit and the
travel is finite (chapter 9). Here the steps carry the players away from
the resting point, by the factor in the last row of the second table of
chapter 13. A game is not a descent.

## What is not shown

- **The whole game.** The best critic is found one input at a time. That
  the maker's loss against the best critic is a distance between the two
  distributions (the Jensen–Shannon divergence) is **recalled** and not
  in Lean.
- **That the slope really grows.** The scores are shown to have no finite
  best value where the data separates. That the critic's slope then
  grows is **argued**.
- **Real networks.** The spiral is for the payoff `x × y`. Near a resting
  point of a real game the same turning is present but mixed with other
  terms (**recalled**).
- **Fixes.** Alternating steps, looking ahead and averaging the weights
  all change the factor `1 + learning_rate²`. None is analysed here. This
  is **open**.

## Check yourself

1. At an input, real data has weight 1 and made data has weight 3. What
   does the best critic predict?
2. With `learning_rate = 0.2`, by what factor is the squared distance
   from rest multiplied in one step? In 25 steps, roughly?
3. At an input real data lands but made data never does. Can training
   settle the critic's score there?

**Answers.** (1) The real share, `1 / (1 + 3) = 0.25`, from
`criticLoss_le_of_sigmoid_eq`. (2) `1 + 0.04 = 1.04`. After 25 steps it
is `1.04 ^ 25`, about 2.7, from `sq_add_sq_iterate_gameStep`. (3) No. By
`strictAnti_criticLoss_of_no_fake` a higher score always has a lower
loss, so the loss keeps asking for a steeper critic.

Previous: [26. The perceptron, XOR and no free lunch](26-the-perceptron.md) · Next: [28. The slope of a network](28-the-slope-of-a-network.md)
