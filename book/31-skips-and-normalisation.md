# 31. Skips and normalisation

**In the repository:**
[`SkipAndNorm.lean`](../lean/SquigglyLine/Supporting/NetworkShape/SkipAndNorm.lean),
[`Residual.lean`](../lean/SquigglyLine/Supporting/NetworkShape/Residual.lean),
note [`skip-and-norm.md`](../docs/supporting/network-shape/skip-and-norm.md).
**You need:** chapters 3, 12 and 14.

## The idea

Two tricks made very deep networks trainable: **skip connections**, where
a layer's input is added to its output, and **normalisation**, where a
layer's output is rescaled to a standard size (**recalled**: He et al.
2016; Ioffe and Szegedy 2015; Ba, Kiros and Hinton 2016). Nearly every
large network uses both. Chapter 14 said what a skip does to slope. This
chapter shows it twice: first in the polarizer picture of chapter 12,
then as a statement about slope.

In the picture, a layer is a plate. Light that meets a plate keeps only
its shadow on the plate's axis. A skip is a **bypass**: part of the beam
goes round the plate and joins the beam that went through. A
normalisation is an **amplifier** after the plate that brings the light
back to full brightness.

> A plate with a bypass never dims the light, and a plate with an
> amplifier never loses it, unless the plate is crossed. A residual layer
> is no steeper than one plus its branch, and a stack of gentle ones
> stays gentle however deep.

## An example you can do by hand

Take light in two dimensions, written `(across, up)`. Let the plate have
axis `(1, 0)`, and let the light be `(3, 4)`.

The overlap of the light with the axis is 3. The shadow is `3 × (1, 0)`,
which is `(3, 0)`. A bare plate gives `(3, 0)`: the length falls from 5
to 3.

With a bypass the output is the light plus the shadow: `(3, 4) + (3, 0)`
is `(6, 4)`. Its squared length is `36 + 16 = 52`. The squared length
before was `25`, and `25 + 3 × 3² = 52`. The part along the axis
doubled and the rest did not move. Send `(6, 4)` through a second
plate with a bypass and you get `(12, 4)`, then `(24, 4)`. The light leans
towards the axis at every plate and never lands on it.

Now a crossed plate. Let the light be `(0, 5)`. The overlap is 0, so a
bare plate gives `(0, 0)`: dark. With a bypass the light comes out
as `(0, 5)`, unchanged.

For the amplifier, light of length 1 along `(1, 0)` meets a plate with
axis `(0.6, 0.8)`. The overlap is 0.6, the shadow is
`0.6 × (0.6, 0.8) = (0.36, 0.48)`, and its length is 0.6. The amplifier
divides by that length and gives `(0.6, 0.8)`. That is the axis, at full
length. Without it, the light would be at 0.6 of its length after one
plate, `0.6 × 0.6 = 0.36` after two plates that turn the same way, and so
on.

## The statement

The first statement says what the bypass does to length.

```lean
/-- The squared length after a plate with a bypass. -/
theorem norm_skipPlate_sq
    (axis_has_length_one : ‖axis‖ = 1)
    (light : Space) :
    let overlap                 := inner ℝ axis light
    let squared_strength_before := ‖light‖ ^ 2
    let squared_strength_after  :=
      ‖PASS_THROUGH_SKIP_PLATE axis light‖ ^ 2
    squared_strength_after
      = squared_strength_before + 3 * overlap ^ 2 := by            -- the part along the axis doubles: `2 ^ 2 - 1 ^ 2 = 3`
```

*Read aloud:* after a plate with a bypass, the squared strength of the
light is what it was, plus three times the squared overlap.

`Space` is any space of vectors with lengths and dot products, so the
statement holds for a flock of any number of activations. `inner ℝ axis
light` is the dot product. `‖light‖` is the length. Because the extra
term is never negative, `norm_le_norm_skipPlate` follows: a plate with a
bypass never dims the light. `skipPlate_of_crossed` says a crossed plate
with a bypass does nothing.

The second statement is about the amplifier.

```lean
/-- **A plate and an amplifier turn the light without loss.** For any turn
short of a right angle, the light comes out along the axis at full
strength. -/
theorem renorm_plate
    (axis_has_length_one : ‖axis‖ = 1)
    (turn_is_under_a_right_angle : 0 < inner ℝ axis light) :       -- a positive overlap: less than 90 degrees from the axis
    let light_after_plate     := PASS_THROUGH_PLATE axis light
    let light_after_amplifier := RENORMALIZE light_after_plate
    light_after_amplifier = axis := by
```

*Read aloud:* if the light has a positive overlap with the axis, then
after the plate and the amplifier it is exactly the axis.

`RENORMALIZE light` is the light divided by its own length. The theorem
`throughNormedPlates_eq` stacks this: with an amplifier after each plate,
full-strength light comes out along the last axis, whatever the sizes of
the turns. And `renorm_plate_of_crossed` says the amplifier cannot revive
light that a crossed plate blocked.

The third statement leaves the picture. It is about slope.

```lean
/-- A residual layer is no steeper than one plus its branch. -/
theorem lipschitzWith_addSkip
    (slope_is_bounded : LipschitzWith slope_limit branch) :
    let layer_slope_limit := 1 + slope_limit  -- the input passes through, the branch adds its own slope
    let layer             := ADD_SKIP branch
    LipschitzWith layer_slope_limit layer := by
```

*Read aloud:* if the branch has slope at most `slope_limit`, the layer
`input + branch(input)` has slope at most `1 + slope_limit`.

`ADD_SKIP branch input` is the Python `input + branch(input)`. The
matching lower bound is `le_dist_addSkip`: two outputs are at least
`1 − slope_limit` times as far apart as their inputs. When `slope_limit`
is below one, `addSkip_injective` says no two inputs give the same
output, and `neverTurns_addSkip` says a one-input layer never turns.

The fourth statement is depth.

```lean
/-- **Depth does not blow up the slope.** If each of `layer_count` branches has
slope at most `exponent / layer_count`, the whole stack has slope at most
`e ^ exponent`, whatever `layer_count` is. -/
theorem dist_runResidualLayers_le_exp
    {branches : ℕ → Space → Space}
    {exponent : ℝ≥0}
    {layer_count : ℕ}
    (slopes_are_bounded :
      ∀ layer_index,
        LipschitzWith (exponent / layer_count) (branches layer_index))
    (input : Space)
    (other_input : Space) :
    let stack        := RUN_RESIDUAL_LAYERS branches layer_count
    let output_gap   := dist (stack input) (stack other_input)
    let input_gap    := dist input other_input
    let growth_limit := Real.exp exponent  -- the most that `layer_count` layers can stretch a gap
    output_gap ≤ growth_limit * input_gap := by
```

*Read aloud:* if you share a fixed slope budget, `exponent`, equally
among the branches of `layer_count` residual layers, then the whole stack
stretches any gap by at most `e` to the power `exponent`, however many
layers there are.

`Real.exp exponent` is `e ^ exponent`, where `e` is about 2.718.

## Why it is true

**The bypass.** The plate keeps the shadow of the light on the axis. The
skip adds it back. So the part of the light along the axis is counted
twice and the part across the axis is counted once. The squared length
is the squared length of the across part plus four times the squared
along part. That is the old squared length plus three times the squared
overlap, which is `norm_skipPlate_sq`. A repeat of the plates doubles
the along part each time and leaves the across part alone
(`inner_iterate_skipPlate`, `iterate_skipPlate_sub_plate`).

**The amplifier.** After a plate the light is the overlap times the axis,
and its length is the size of the overlap. The amplifier divides by that
length. If the overlap is positive, what is left is the axis itself. This
is one line in the Lean proof, and `throughNormedPlates_eq` is an
induction on it: the light arrives on the last axis, so one more plate
and amplifier put it on the next.

**The slope.** The layer's gap is the input gap plus the branch gap. The
branch gap is at most `slope_limit` times the input gap, so the total is
at most `1 + slope_limit` times it. For the lower bound, the branch can
undo at most `slope_limit` of the input gap, and the skip keeps all of
it.

**The depth.** One layer with branch slope `exponent / layer_count`
stretches a gap by at most `1 + exponent / layer_count`. The stack
stretches by at most that, raised to the power `layer_count`. The proof
`one_add_div_pow_le_exp` shows that this is never more than
`e ^ exponent`. A plain stack of layers with slope `exponent /
layer_count` each would multiply to a power of a number that can be far
below one.

## What it explains

Why networks with skips can be deep. In the picture, no single plate can
kill the signal, and the light leans towards each axis a little at a
time instead of snapping onto it. That is the kind of path chapter 17
found to lose least. In slope, a gentle branch cannot merge points, and
a deep stack has bounded slope.

Why networks use normalisation as well. A bypass alone lets the light
grow, since each plate can only add length. An amplifier alone is helpless
after a crossed plate. Together they keep a signal alive and keep its
size fixed. This is the note's reading, and it is a reading: the proof
says what each piece does, not that this is why designers chose both.

The same fact holds through time. The memory cell of an LSTM keeps a share
of itself at every step. Its slope per step is that share, never above
one (`abs_updateCell_sub_le`), and exactly one with the gate fully open
(`updateCell_sub_of_open_gate`). An open gate is a skip through time.

## How this meets the squiggly line

Through **slope** (chapter 3) and the picture of **layers as polarizers**
(chapter 12). A skip adds one to the slope of its branch, and a stack of
them stays inside `e ^ exponent`. A fold merges points, as chapter 8
showed. A skip with a gentle branch cannot, so squiggle has to be bought
in the branch, where the slope is above one. That is the third answer of
chapter 14: a skip adds one.

## What is not shown

- **Which normalisation.** The amplifier rescales one example to a
  standard length. That is closest to layer normalisation and RMSNorm.
  Batch normalisation rescales each feature across a batch. It is a
  different operation and it is not modelled here (**open**).
- **ReLU.** A plate keeps the shadow on a line. A ReLU layer keeps the
  nearest point in a quadrant. The statements here are for plates.
- **Real optics.** Joining two beams and amplifying light both have
  costs that the picture leaves out. It is a picture of the arithmetic,
  not a design (**open**).
- **Training.** Nothing here is about how these tricks change gradient
  descent (**open**).

## Check yourself

1. Light `(1, 2)` meets a plate with axis `(1, 0)` and a bypass. What
   comes out, and what is its squared length?
2. A residual layer has a branch of slope at most 0.5. Two inputs are 4
   apart. Between what values must the outputs be?
3. Four residual layers share a slope budget `exponent` of 2, so each
   branch has slope at most 0.5. How far apart can the outputs of the
   stack be, if the inputs are 1 apart?

**Answers.** (1) The overlap is 1, the shadow is `(1, 0)`, so the output
is `(2, 2)`. Its squared length is 8, and `‖(1, 2)‖² + 3 × 1² = 5 + 3 =
8`, as `norm_skipPlate_sq` says. (2) By `lipschitzWith_addSkip` and
`le_dist_addSkip` the gap is between `0.5 × 4 = 2` and `1.5 × 4 = 6`.
(3) At most `e ^ 2`, about 7.39, by `dist_runResidualLayers_le_exp`. (The
plain product bound is `1.5 ^ 4`, about 5.06, which is smaller here:
the theorem gives a bound that holds for every `layer_count`, not the best
one for four.)

Previous: [30. Signals through depth](30-signals-through-depth.md) · Next: [32. Depth against width](32-depth-against-width.md)
