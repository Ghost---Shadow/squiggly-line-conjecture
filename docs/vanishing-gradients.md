# Vanishing and exploding signals

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/VanishingGradients.lean` unless another file is named),
**recalled**, or **open**.

## The idea

Deep networks were hard to train for a long time because the signal died or
blew up on its way through the layers, and the gradient did the same on its
way back (**recalled**: Hochreiter 1991; Bengio, Simard and Frasconi 1994).
The cures were careful starting weights, skip connections and normalisation
(**recalled**: Glorot and Bengio 2010; He et al. 2015).

In the polarizer picture all of this is one piece of arithmetic.

## One number per layer

Suppose each layer multiplies the size of the signal by a gain `g`. After `L`
layers the size has been multiplied by `g^L`.

- **Below one, it dies.** `g^L` is at most `e^(−L(1 − g))`. The loss is
  exponential in the depth (**proved**: `gain_pow_le_exp`).
- **Above one, it blows up.** `g^L` is at least `1 + L(g − 1)`, so it grows
  without limit (**proved**: `one_add_mul_le_gain_pow`).

Only a gain of exactly one survives every depth. This is why the starting
weights are chosen to keep the size of the signal the same from layer to
layer.

## Plates dim

A polarizer plate never lengthens the light (**proved**: `norm_plate_le`). A
plate turned by `θ` from the light keeps `cos θ` of it, so a stack of `L`
plates with a fixed turn has gain `cos θ` at each one and the light dies
exponentially (**proved**: `plates_vanish`).

The way out found in `small-steps.md` is to make the turns smaller as the
stack gets deeper. Then the gain at each plate moves towards one fast enough.

## The gradient comes back through the same plates

Training needs to know how the output changes when the input changes. For a
stack of plates the answer is: send the read-out direction backwards through
the same plates, in the opposite order
(**proved**: `inner_plate_comm` for one plate, `inner_runPlates` for a
stack).

So the gradient is dimmed by the same plates as the signal. A stack that
loses the signal going forward loses the gradient coming back. Vanishing
signals and vanishing gradients are one fact.

## A bypass blows up

A plate with a bypass, which is a skip connection, doubles the part of the
light along its axis. After `k` of them on one axis the light is at least
`2^k` times as long as its first overlap with that axis
(**proved**: `le_norm_iterate_skipPlate`). So skip connections cure the dying
and cause the opposite.

## An amplifier holds it at one

A plate followed by an amplifier, which is a normalisation, gives light of
length exactly one at every depth (**proved** earlier:
`throughNormedPlates_eq` in `SkipAndNorm.lean`).

That gives the full picture of why the usual recipe has both parts.

| Layer | Gain | What happens with depth |
|---|---|---|
| Plate | below one | dies |
| Plate with a bypass | above one | blows up |
| Plate with a bypass and an amplifier | held at one | survives |

## How this meets the squiggly line

A squiggly path needs many layers, and many layers need the signal to
survive them. The gain is what decides whether depth can be used at all.

## What is not shown

- **ReLU layers.** A ReLU layer with random weights halves the signal's
  squared size on average, and the usual starting weights are scaled up to
  cancel that (**recalled**). Here the layers are plates.
- **The gradient for ReLU.** The backward pass of a ReLU network also
  switches off where the forward pass was zero. Not modelled.
- **Recurrent networks.** The same count applies to steps in time, but it is
  not written out.
