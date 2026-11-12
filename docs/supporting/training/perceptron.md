# The perceptron, XOR and no free lunch: nearness to a boundary

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/Supporting/Training/Perceptron.lean` unless another file is named),
**argued**, **recalled**, or **open**.

## The idea

The theorem is about the distance from the data to a line. A classifier has
a line too: its boundary, where the score is zero. The distance from the data
to the boundary is called the **margin**. Three old results are statements
about that distance.

## The margin is a nearest-point distance

Take a flat boundary through the origin, at right angles to a direction `u`
of length one. A point whose score against `u` is `s` lies at least `|s|`
from the boundary (**proved**: `abs_inner_le_infDist_flatBoundary`).

So "every example scores at least `γ` on its correct side" means "no example
is nearer than `γ` to the boundary". The margin is the nearest-point distance
of the theorem, measured to a boundary.

## The perceptron: nearness sets the number of steps

The perceptron is the oldest learning rule (**recalled**: Rosenblatt 1958).
Whenever it gets an example wrong, it adds that example to its weights, with
the sign of its label.

Suppose the examples lie within `R` of the origin, and some flat boundary
keeps every one of them at least `γ` away on its correct side. Then

- each mistake moves the weights at least `γ` along the true direction
  (**proved**: `mul_margin_le_inner`), and
- each mistake adds at most `R²` to the squared size of the weights
  (**proved**: `norm_sq_perceptronWeights_le`).

The first grows like the number of mistakes and the second like its square
root. They cannot both go on, so the perceptron makes at most

```
(R / γ)²  mistakes
```

(**proved**: `perceptron_mistake_bound`; the result is Novikoff's, 1962,
**recalled**.)

This is the rule of the whole repository in its first form. The work of
training is set by a distance. Data that sits near the boundary is slow to
learn, and data that sits far from it is fast. The number of parameters does
not appear.

## XOR: when no flat boundary is near enough

Four points: `(0,0)` and `(1,1)` are "no", `(0,1)` and `(1,0)` are "yes". No
flat boundary splits them (**proved**: `not_separatesXor_flat`; **recalled**:
Minsky and Papert 1969). The margin is not small here. It does not exist.

There are two repairs, and they are the two ways this repository makes a
squiggly line.

- **A lift.** Add the product `x·y` as a third feature. Upstairs the boundary
  is flat (**proved**: `separatesXor_lift`). This is
  `docs/networks/kernel-trick.md`.
- **A fold.** Fold the plane along the line `x = y`, which is what `|x − y|`
  does. After the fold a flat boundary works (**proved**:
  `separatesXor_fold`). This is one ReLU layer, as in `Depth.lean`.

## No free lunch: squiggle helps only if labels vary gently

Fix an input the model has not seen, and any guess at its label. Among all
the possible ways to label the inputs, exactly half agree with the guess
there (**proved**: `card_agree_eq_card_disagree`; **recalled**: Wolpert
1996). So with no assumption about the labels, no learner beats a coin on
unseen inputs.

In the terms of the line: if an unseen label is `+1` or `−1` with equal
chance, a prediction `h` costs `h² + 1` on average (**proved**:
`mean_sq_error_unseen`). The best line is flat at zero, and every bend away
from it only adds.

So nothing here can say that a squigglier line is better in general. A line
through the training points helps on new points only when nearby inputs have
nearby labels, that is, when the truth itself has a bounded slope. That
assumption is where every result about new inputs in this repository gets its
content (`docs/supporting/new-inputs/`).

## What is not shown

- **A perceptron with a moving lift.** The bound is for fixed features.
- **Margins for boundaries that are not flat.** For a score of slope `K` the
  matching statement is `le_mul_dist_of_flip` in `NetworkSlope.lean`.
- **How large the margin of real data is** after a network's lift. **open**
- **A bound on test error from the margin.** Known (**recalled**: Vapnik),
  not formalised.
