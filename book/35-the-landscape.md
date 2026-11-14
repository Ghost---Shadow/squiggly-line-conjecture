# 35. The landscape: connected fits and collapsed classes

**In the repository:**
[`ModeConnectivity.lean`](../lean/SquigglyLine/Supporting/NetworkShape/ModeConnectivity.lean),
[`NeuralCollapse.lean`](../lean/SquigglyLine/Supporting/NetworkShape/NeuralCollapse.lean),
notes [`mode-connectivity.md`](../docs/supporting/network-shape/mode-connectivity.md) and
[`neural-collapse.md`](../docs/supporting/network-shape/neural-collapse.md).
**You need:** chapters 9, 10 and 14.

## The idea

Train the same network twice from different starts. You get two sets of
weights that both fit. Walk in a straight line from one to the other. Often
the loss rises on the way: there is a hill between them. People have
reported that the two fits can still be joined by a curved path with no
hill (**recalled**: Garipov et al. 2018; Draxler et al. 2018), and that
after relabelling the neurons, even the straight line has no hill
(**recalled**: Entezari et al. 2022; Ainsworth et al. 2023). The last claim
is a conjecture.

Keep training a classifier long after it gets every training label right,
and its last layer is reported to settle into a tidy shape: one point for
each class, the points as far apart as they can be (**recalled**: Papyan,
Han and Donoho 2020). This is **neural collapse**.

The repository does not prove either report. It proves the small exact
statements that sit under them.

> A model linear in its weights has no hill between two fits. With two
> weights multiplied, the hill is exactly the product of how far the fits
> differ in each. And for any number of classes, arrows of length one
> cannot all overlap by less than minus one over the number of other
> classes.

## An example you can do by hand

**The hill.** The model is one weight times another, `first × second`. Both
`(2, 3)` and `(3, 2)` give 6, so both fit the target 6. Halfway along the
line the weights are `(2.5, 2.5)`, and the output is `6.25`. It is off by
`0.25`. The formula below gives the hill as
`0.25 × (2 − 3) × (3 − 2) = −0.25`, and `6 − (−0.25) = 6.25`.

The worst case is a fit and its mirror. `(2, 3)` and `(−2, −3)` both give 6.
Halfway, the weights are `(0, 0)` and the output is 0, whatever the target.

**The arrows.** Three arrows of length one, at 120 degrees to each other in
a plane, overlap by `−0.5` each. They add up to zero. You cannot do better:
the limit for three classes is `−1 / 2`.

## The statement

Here is the hill for two weights multiplied.

```lean
theorem twoLayer_along
    {first_a first_b second_a second_b target : ℝ}
    (first_fits : first_a * first_b = target)
    (second_fits : second_a * second_b = target)
    (fraction : ℝ) :
    let blended_a      := (1 - fraction) * first_a + fraction * second_a
    let blended_b      := (1 - fraction) * first_b + fraction * second_b
    let output         := blended_a * blended_b
    let hill           :=
      fraction * (1 - fraction)
        * ((first_a - second_a) * (first_b - second_b))  -- largest halfway along, zero at both fits
    let expected_output := target - hill
    output = expected_output := by
```

*Read aloud:* a fraction of the way between two fits of the same target,
the output is the target minus `fraction × (1 − fraction)` times the
difference in the first weight times the difference in the second.

The names `first_a` and `first_b` are the two weights of the first fit, and
`second_a` and `second_b` those of the second. For a model that is linear
in its weights there is no such term. The theorem `no_barrier` says the
error anywhere on the line is no larger than at the worse end, and
`fit_along` says the line between two fits is all fits.

Here is the limit on how far apart the classes can be.

```lean
theorem neg_one_le_of_inner_le
    [Nonempty Classes]
    {arrows : ClassArrows Classes Space}
    (arrows_have_length_one : ∀ this_class, ‖arrows this_class‖ = 1)
    {overlap_limit : ℝ}
    (overlaps_at_most_limit :
      ∀ this_class other_class, this_class ≠ other_class →
        inner ℝ (arrows this_class) (arrows other_class) ≤ overlap_limit) :
    let class_count : ℝ   := Fintype.card Classes
    let other_class_count := class_count - 1
    let lowest_possible : ℝ := -1                                  -- the simplex: every overlap is `-1 / other_class_count`
    lowest_possible ≤ other_class_count * overlap_limit := by      -- a squared length is never negative
```

*Read aloud:* if every pair of class arrows overlaps by at most
`overlap_limit`, then the number of other classes times `overlap_limit` is
at least minus one.

`inner ℝ` is the overlap of two arrows: 1 if they point the same way, 0 at
a right angle, minus 1 if opposite. `ClassArrows` is one arrow for each
class. The arrangement that reaches the limit is the **simplex**, and
`sum_eq_zero_iff_of_equiangular` says that evenly spread arrows reach the
limit exactly when they add up to zero.

## Why it is true

**No hill.** The model is linear, so its outputs blend like the weights do.
Midway along the line the error is the same blend of the two errors
(`residual_along_between`). A blend of two zero errors is zero, and a
blend is never larger than the larger of the two.

**The hill.** Write the output at the blended weights and multiply it out.
Both fits give the target, so the terms with the target collect together,
and what is left is `fraction × (1 − fraction)` times the product of the
differences. The Lean proof is one `linear_combination` of the two
statements that the fits fit.

**The mirror.** If `(a, b)` fits, so does `(−a, −b)`, because the two signs
cancel (`twoLayer_flip`). Halfway between them both weights are zero
(`twoLayer_midpoint_mirror`). But the mirror is the same function. The hill
comes from writing one function in two ways.

**The arrows.** Add up all the arrows. The squared length of the sum is the
number of arrows, one from each arrow's own length, plus the overlaps of
every pair (`norm_sum_sq_eq_sum_inner`). A squared length is never
negative. So if every overlap is at most `overlap_limit`, the sum is at most
`class_count × (1 + other_class_count × overlap_limit)`, and that cannot be
below zero.

## What it explains

**Why straight lines can be bad.** In a real network, relabelling the
neurons plays the part of the sign flip. Two networks may compute nearly
the same function with their neurons in another order. The straight line
between them mixes unlike neurons, and the loss rises. Line the neurons up
first and the hill may go. The two-weight model shows this exactly for the
sign flip. That it always happens for wide networks is the conjecture, and
it stays **open**.

**Why the class points sum to zero.** Part of the shape in neural collapse
is plain geometry. The farthest-apart arrangement is the centred one. And
the counting result of chapter 34, `merged_iff_label_eq`, gives the first
part in counting form: a layer squeezed to as many places as labels has one
place for each class.

## How this meets the squiggly line

The hill is a product of two differences, and a product only appears when
weights multiply. So it is depth, the thing that made the model squiggly,
that made the hill. A model linear in its weights is the lift of chapter
11 with the features held fixed, and chapter 10 showed its fits form one
flat sheet. How far a point must be pushed to change its label depends on
how far apart the class points are, which is the nearness of chapter 4. The
simplex makes that distance as large as it can be for every pair at once.

## What is not shown

- **Real networks.** The no-hill result is for models linear in their
  weights. The hill is shown for two weights multiplied. **open**
- **That shuffling neurons removes the hill.** It is shown here only for
  the sign flip of the two-weight model. **open**
- **Curved paths.** That fits of a deep network can be joined by a curved
  path with no hill is not addressed. **open**
- **That training goes to the simplex.** The geometry is proved. That the
  last layer of a trained network lands there is reported for simplified
  models where the last-layer features are free to move (**recalled**, not
  checked here). For real networks it is an observation. **open**

## Check yourself

1. Two fits of the target 6 are `(1, 6)` and `(3, 2)` for the model
   `first × second`. What is the output halfway along the line between
   them?
2. For five classes, what is the lowest overlap that every pair of arrows
   of length one can reach at once?
3. A model is linear in its weights, and two settings of the weights both
   fit the data exactly. What is the error at a point a third of the way
   between them?

**Answers.** (1) The halfway weights are `(2, 4)`, so the output is 8. By
`twoLayer_along` it is `6 − 0.25 × (1 − 3) × (6 − 2)`, which is
`6 + 2 = 8`. (2) By `neg_one_le_of_inner_le`, four times the limit is at
least `−1`, so it is `−1 / 4`. (3) Zero, by `fit_along`: the line between
two fits is all fits.

Previous: [34. Capacity and compression](34-capacity-and-compression.md) · Next: [36. Attention](36-attention.md)
