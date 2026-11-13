# Vanishing and exploding signals

**Proofs:** [`MarkovChains.lean`](../../../lean/SquigglyLine/Networks/MarkovChains.lean), [`Activations.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/Activations.lean), [`SkipAndNorm.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/SkipAndNorm.lean), [`VanishingGradients.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/VanishingGradients.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/NetworkShape/VanishingGradients.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/VanishingGradients.lean) unless another file is named),
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

The way out found in `docs/supporting/training/small-steps.md` is to make the turns smaller as the
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
`throughNormedPlates_eq` in [`SkipAndNorm.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/SkipAndNorm.lean)).

That gives the full picture of why the usual recipe has both parts.

| Layer | Gain | What happens with depth |
|---|---|---|
| Plate | below one | dies |
| Plate with a bypass | above one | blows up |
| Plate with a bypass and an amplifier | held at one | survives |

## How this meets the squiggly line

A squiggly path needs many layers, and many layers need the signal to
survive them. The gain is what decides whether depth can be used at all.

## Activations, one by one

Notes from 14 Nov 2026. Proofs in
[`lean/SquigglyLine/Supporting/NetworkShape/Activations.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/Activations.lean).

The slope of a layer is the slope of its weights times the slope of its
activation. The activation's share is fixed by which one it is.

- **Sigmoid.** Its slope is `s * (1 - s)`, where `s` is its output. That is
  never above one quarter (**proved**: `sigmoid_mul_one_sub_le`,
  `lipschitzWith_sigmoid`). So `L` sigmoid layers in a row have slope at
  most `(1/4)^L` (**proved**: `lipschitzWith_iterate_sigmoid`). Unless the
  weights are large enough to make up a factor of four at every layer, the
  gradient dies with depth. This is the saturation that ReLU was brought in
  to avoid (**recalled**: Glorot and Bengio 2010; Nair and Hinton 2010).
- **ReLU.** Its slope is one where it is open and zero where it is closed.
  It costs nothing where it is open, and a unit that is closed for every
  input is dead ([`MarkovChains.lean`](../../../lean/SquigglyLine/Networks/MarkovChains.lean)).
- **Leaky ReLU.** Its slope is one where the input is positive and `leak`
  where it is not. So it never rises by more than its input does
  (**proved**: `leakyRelu_sub_le`) and never by less than `leak` times that
  (**proved**: `le_leakyRelu_sub`). With a positive leak it is always
  rising: it merges no two inputs and cannot go dead (**proved**:
  `strictMono_leakyRelu`).
- **Max pooling.** The higher of two lines is no steeper than the steeper of
  them (**proved**: `lipschitzWith_max`). Pooling adds no slope.
- **Spectral normalisation.** A layer divided by its own size has size at
  most one, and so slope at most one (**proved**:
  `norm_spectralNormalize_le`, `lipschitzWith_spectralNormalize`). This is a
  cap on slope put in by hand, as in a Wasserstein critic.

Not shown: tanh, whose slope is at most one, and pooling over more than two
lines, which follows by repeating the step for two.

## What is not shown

- **ReLU layers.** Here the layers are plates. That a ReLU layer halves the
  squared size of a signal that is as often negative as positive, and that
  the usual starting weights are scaled up to cancel it, is proved in
  `gain.md`.
- **The gradient for ReLU.** The backward pass of a ReLU network also
  switches off where the forward pass was zero. Not modelled.
- **Recurrent networks.** The same count applies to steps in time. It is
  written out for the memory cell of an LSTM in `skip-and-norm.md`, and not
  for a plain recurrent network.
