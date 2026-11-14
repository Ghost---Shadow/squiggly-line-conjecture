# 26. The perceptron, XOR and no free lunch

**In the repository:**
[`Perceptron.lean`](../lean/SquigglyLine/Supporting/Training/Perceptron.lean),
note [`perceptron.md`](../docs/supporting/training/perceptron.md).
**You need:** chapters 3, 4, 8 and 11.

## The idea

The theorem is about the distance from the data to a line. A classifier
has a line too: its **boundary**, where the score is zero. Points on one
side are "yes" and points on the other are "no". The distance from the
data to that boundary is called the **margin**.

Three old results are statements about this distance. The
**perceptron**, the oldest learning rule, adds each example it gets
wrong to its weights, with the sign of its label (**recalled**:
Rosenblatt 1958). **XOR** is the puzzle that no flat boundary splits
four points. **No free lunch** says that with no assumption about the
labels, no learner beats a coin on unseen inputs.

> A perceptron makes at most `(radius / margin)²` mistakes. A flat
> boundary cannot split XOR, but one lifted feature or one fold can.
> And over all possible labellings, every guess at an unseen input is
> right exactly half the time.

## An example you can do by hand

**Mistakes.** Suppose every example lies within `radius = 10` of the
origin, and some flat boundary keeps each one at least `margin = 2` away
on its correct side. The bound is `(10 / 2)² = 25`. However many examples
there are, the perceptron makes at most 25 mistakes.

Halve the margin to 1 and the bound is `(10 / 1)² = 100`: four times as
many.

**XOR.** Try a flat score `first_weight × first + second_weight ×
second + bias` with weights 1, 1 and bias `−1`. At the corners
`(0, 0)`, `(1, 1)`, `(0, 1)`, `(1, 0)` it gives `−1`, `1`, `0`, `0`. XOR
wants the first two negative and the last two positive. For any weights,
the first two scores add up to the same number as the last two, so one
sum cannot be negative while the other is positive. The fold
`|first − second| − 1/2` gives `−1/2`, `−1/2`, `1/2`, `1/2`: right.

**No free lunch.** Take three inputs, each labelled yes or no: `2 × 2 ×
2 = 8` labellings. Guess "yes" at the first input. Four labellings agree
and four disagree.

## The statement

```lean
/-- **The perceptron makes at most `(radius / margin)²` mistakes.** The
examples lie within `radius` of the origin, and some direction of length at
most one scores every one of them at least `margin` on its correct side. -/
theorem perceptron_mistake_bound
    {mistakes : ℕ → Space}
    {true_direction : Space}
    {margin radius : ℝ}
    {mistake_count : ℕ}
    (true_direction_is_short : ‖true_direction‖ ≤ 1)  -- so that `margin` is a distance, not a rescaled one
    (margin_pos : 0 < margin)
    (every_example_clears_the_margin :
      ∀ index < mistake_count,
        margin ≤ inner ℝ true_direction (mistakes index))
    (every_example_was_a_mistake :
      ∀ index < mistake_count,
        inner ℝ (GET_PERCEPTRON_WEIGHTS mistakes index) (mistakes index) ≤ 0)
    (every_example_is_within_radius :
      ∀ index < mistake_count, ‖mistakes index‖ ≤ radius) :
    let mistake_limit := (radius / margin) ^ 2  -- squared: progress grows like the count, size only like its square root
    (mistake_count : ℝ) ≤ mistake_limit := by
```

*Read aloud:* if the perceptron has made `mistake_count` mistakes, then
`mistake_count` is at most `(radius / margin)²`.

`mistakes i` is the `i`th example it got wrong, times its label, plus or
minus one. `GET_PERCEPTRON_WEIGHTS mistakes index` is the sum of the
first `index` of them. Being a mistake means the dot product of the
weights with the example was not positive.

The margin really is a nearest distance. A point whose score against a
direction of length at most one is `score` lies at least `|score|` from
the flat boundary (`abs_inner_le_infDist_flatBoundary`).

```lean
/-- **No flat boundary splits XOR.** -/
theorem not_separatesXor_flat
    (first_weight second_weight bias : ℝ) :
    let flat_score : ScoreFunction := fun first second =>
      first_weight * first + second_weight * second + bias  -- zero along a straight line
    ¬SEPARATES_XOR flat_score := by
```

*Read aloud:* for any weights and any bias, a flat score is not negative
at `(0, 0)` and `(1, 1)` and positive at `(0, 1)` and `(1, 0)` all at
once.

The two repairs are `separatesXor_lift`, with the product `first ×
second` as a third feature, and `separatesXor_fold`, with the fold
`|first − second|`.

The no free lunch statement is `card_agree_eq_card_disagree`. For labels
plus or minus one with equal chance, `mean_sq_error_unseen` says a
prediction costs `prediction² + 1` on average.

## Why it is true

**The perceptron.** Two facts about the weights are proved, one for each
mistake.

First, each mistake moves the weights at least `margin` along the true
direction (`mul_margin_le_inner`). The example clears the margin, and the
weights gain exactly the example. After `mistake_count` mistakes the weights have
moved at least `mistake_count × margin` along that direction.

Second, each mistake adds at most `radius²` to the squared size of the
weights (`norm_sq_perceptronWeights_le`). The new squared size is the old
one, plus twice the dot product of the old weights with the example,
plus the example's own squared size. The middle term is not positive,
because the example was a mistake. So after `mistake_count` mistakes the squared size
is at most `mistake_count × radius²`, and the size is at most `√mistake_count × radius`.

The first grows like `mistake_count` and the second like `√mistake_count`. So
`mistake_count × margin ≤ √mistake_count × radius`, which gives
`mistake_count ≤ (radius / margin)²`.

**XOR.** The scores at `(0, 0)` and `(1, 1)` add to `2 × bias +
first_weight + second_weight`, and so do the other two. The lift and the
fold are checked by putting in the four corners. For no free lunch,
flipping the label at `input` pairs each agreeing labelling with a
disagreeing one (`flipAt_flipAt`).

## What it explains

**Why hard data is slow.** The work is set by a distance. Data near the
boundary is slow to learn. The number of parameters does not appear.

**Why a hidden layer was needed.** For XOR the margin does not exist:
no flat boundary has one. A hidden layer is a fold, and a fold is one
way to make a flat boundary work. The lift is the other.

Two encodings seem to avoid a hidden layer, but each hides a lift. One
input per corner fits any labels (`oneHot_fits`), but making those inputs
is the lift. One class per corner names the nearest corner
(`anchorScore_le_iff`), but reading XOR off the outputs is a second step.

**Why results about new inputs need an assumption.** With no assumption
about the labels, a squigglier line is no better than a flat one. It
helps only when nearby inputs have nearby labels, that is, when the
truth has bounded slope. Part VII builds on that.

## How this meets the squiggly line

Three of the six ideas. **Nearness** (chapter 4): the margin is the
nearest distance to a boundary, and the mistake bound is built from it.
**Folds** (chapter 8): one fold splits XOR. **The lift** (chapter 11):
the product feature splits XOR, and so does the table lookup. The lift
and the fold are the two ways this repository makes a squiggly line.

## What is not shown

- **A perceptron with a moving lift.** The bound is for fixed features.
- **Margins for boundaries that are not flat.** For a score of bounded
  slope the matching statement is `le_mul_dist_of_flip` in
  `NetworkSlope.lean`.
- **How large the margin of real data is** after a network's lift. This
  is **open**.
- **A bound on test error from the margin.** Known (**recalled**:
  Vapnik), not in Lean. The mistake bound is Novikoff 1962 (**recalled**).

## Check yourself

1. Examples lie within 6 of the origin and the margin is 1.5. At most how
   many mistakes?
2. A flat score has `first_weight = 2`, `second_weight = 2` and
   `bias = −3`. At `(0, 0)` and `(1, 1)` it is `−3` and `1`. What are the
   scores at the other two corners, and what does that show?
3. There are four inputs. How many labellings agree with the guess "yes"
   at one chosen input?

**Answers.** (1) `(6 / 1.5)² = 16`, from `perceptron_mistake_bound`.
(2) Both are `2 − 3 = −1`. The sums are `−3 + 1 = −2` and
`−1 + −1 = −2`, equal. XOR needs the last two positive, and they are
not, as `not_separatesXor_flat` says. (3) There are `2⁴ = 16`
labellings, and by `card_agree_eq_card_disagree` half agree: 8.

Previous: [25. Classification](25-classification.md) · Next: [27. Two players: the GAN game](27-two-players.md)
