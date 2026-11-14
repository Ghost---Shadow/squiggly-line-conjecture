# 17. The shortest trip

**In the repository:**
[`LeastAction.lean`](../lean/SquigglyLine/Supporting/Training/LeastAction.lean),
note [`least-action.md`](../docs/supporting/training/least-action.md).
**You need:** chapters 9, 10 and 12.

## The idea

Physics has an old rule, the principle of least action: a ball rolls
along the path that costs least. It is natural to ask whether training
does the same. A network is trained a step at a time, so what it arrives
at should be, in some sense, the cheapest place to arrive.

For a model that is linear in its weights, the idea can be made exact.
Chapter 9 measured the **travel** to a fit: how far the weights must
move. Gradient descent never wastes movement. Each step moves the weights
only along the features, and a move along the features is the shortest way
to change the outputs.

> If gradient descent arrives at a fit, no other fit is nearer to where
> it started.

The same idea holds, in a smaller way, for the polarizers of chapter 12.
Of two plates that turn the light by different angles, the pair that
turns by the average of the two angles keeps at least as much light.

## An example you can do by hand

One data point and two weights. The model is `output = weight_1 +
weight_2`, so its features are `(1, 1)`. The label is 4 and the start is
`(1, 0)`, so the output is 1 and the error is 3.

Every fit lies on the line `weight_1 + weight_2 = 4`. With learning rate
0.5, one gradient step adds `0.5 × 3 × (1, 1)`, which is `(1.5, 1.5)`.
The weights land on `(2.5, 1.5)`, and 2.5 + 1.5 = 4. The travel is
`√(1.5² + 1.5²) = √4.5`, about 2.12.

Now compare two other fits. `(4, 0)` needs a move of `(3, 0)`: travel 3.
`(0, 4)` needs a move of `(−1, 4)`: travel `√17`, about 4.12. Gradient
descent found the nearest of the three. It had to, because its move
`(1.5, 1.5)` points along the features `(1, 1)`, and the line of fits is
at right angles to that.

For the polarizers, take turns of 60° and 0°. The pair keeps
`cos 60° × cos 0° = 0.5 × 1 = 0.5`. Two turns of the average, 30°, keep
`cos 30° × cos 30° = 0.75`. The even pair keeps more.

## The statement

```lean
theorem gradientDescent_fit_is_nearest
    (predict : Weights →L[ℝ] Outputs)
    (labels : Outputs)
    (learning_rate : ℝ)
    (start_weights : Weights)
    (step_count : ℕ)
    (trained_weights_fit :
      predict ((TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights) = labels)
    {other_weights : Weights}
    (other_weights_fit : predict other_weights = labels) :
    let trained_weights :=
      (TAKE_GRADIENT_STEP predict labels learning_rate)^[step_count]
        start_weights
    let trained_distance := ‖trained_weights - start_weights‖
    let other_distance   := ‖other_weights - start_weights‖
    trained_distance ≤ other_distance := by
```

*Read aloud:* if training for `step_count` steps lands on a fit, then
any other fit is at least as far from the start. The bars `‖ ‖` are the
length of a move, as in chapter 9. `[step_count]` on the step means
"apply it that many times".

The second statement is for the layers.

```lean
theorem cos_mul_cos_le_cos_half_sq
    (first_turn : ℝ)
    (second_turn : ℝ) :
    let kept_by_two_turns := cos first_turn * cos second_turn
    let average_turn      := (first_turn + second_turn) / 2
    let kept_by_average   := cos average_turn ^ 2
    kept_by_two_turns ≤ kept_by_average := by
```

*Read aloud:* two turns never keep more than two turns of their
average. `even_turns_keep_more` is the same with a length in front.

## Why it is true

**Moving along the features.** After any number of steps, the weights
differ from the start by a move of the form `adjoint predict vector`, the
transpose of chapter 10 applied to some vector of outputs
(`exists_iterate_gradientStep`). The proof is by counting steps. One more
step adds a multiple of the error, and the error is itself pulled back by
the transpose.

**Why that move is shortest.** Call the move training made `move`, and
let `other_move` be the move to another fit. Both fits give the same
outputs, so the model sends `move` and `other_move` to the same place.
Because `move` lies along the features, its inner product with
`other_move` can be taken on the output side, where the two agree. So

```
‖move‖² = inner(move, other_move) ≤ ‖move‖ × ‖other_move‖
```

The last step is the Cauchy–Schwarz inequality of chapter 3. Divide by
`‖move‖` and you have `‖move‖ ≤ ‖other_move‖`
(`norm_sub_le_of_fit_along_features`).

**The plates.** The product of two cosines is half the sum of the cosine
of their difference and the cosine of their sum. Two turns of the average
keep `1/2` plus half the cosine of the sum. The two differ only in the
cosine of the difference, and a cosine is at most 1.

## What it explains

People often say that gradient descent has an **implicit bias**: of all
the fits, it prefers some. Here the preference is exact for a linear
model. It prefers the fit nearest the start, and the function it ends with
stays as close as possible to the starting function. That is why
`exists_fit_near_start` of chapter 10 has a leash on the fit.

For the layers, the note says a trained network with skip connections is
reported to take straighter paths as it trains (**recalled**: Hosseini
and Fedorenko). The plate inequality gives the reason such a path would
lose least. It does not show that trained layers do turn evenly.

## How this meets the squiggly line

The travel of chapter 9 is the cost the squiggly line has to pay, and
here it becomes the cost training actually pays. The transpose is the
lift-and-kernel machinery of chapters 10 and 11: the move lives in the
space the features span. The plates are the polarizers of chapter 12,
where a layer keeps only part of a signal.

## What is not shown

- **Deep networks.** The first result is for models that are linear in
  their weights. For a real network, gradient descent is known to favour
  some solutions, but "the nearest fit" is exact only in the linear case.
  This is **open**.
- **Reaching the fit.** Gradient descent usually approaches a fit
  without landing on it. The statement covers the case where it lands.
- **More than two plates.** The comparison is for a neighbouring pair.
  That equal steps are best among `N` plates follows by repeating it,
  and that last step is argued, not proved. **open**
- **That trained layers turn evenly.** That is an observation from the
  literature, not derived here. **open**

## Check yourself

1. In the example, the label is 4 and the start is `(0, 0)`. Where does
   one step with learning rate 0.5 land, and which fit is nearest?
2. Why can gradient descent not land on a fit that is further than
   another fit when both are available?
3. Turns of 90° and 0° meet two turns of 45°. What does each pair keep?

**Answers.** (1) The error is 4, so the step adds `0.5 × 4 × (1, 1)`,
which is `(2, 2)`. The output is 4, so it is a fit, and by
`gradientDescent_fit_is_nearest` it is the nearest. Check: `(4, 0)` is
at distance 4, and `(2, 2)` is at `√8`, about 2.83. (2) Its move lies
along the features, and `norm_sub_le_of_fit_along_features` shows a fit
reached that way is at least as near as any other. (3) `cos 90° ×
cos 0° = 0`, and `cos 45° × cos 45° = 0.5`. The even pair keeps more, as
`cos_mul_cos_le_cos_half_sq` says.

Previous: [16. New inputs](16-new-inputs.md) · Next: [18. Strong directions first](18-strong-directions-first.md)
