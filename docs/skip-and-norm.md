# Skip connections and normalisation, as polarizers

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/SkipAndNorm.lean`), **recalled**, or **open**.

## The question

In the polarizer picture a layer is a plate. Light that meets a plate keeps
only its shadow on the plate's axis. A turn of angle `a` keeps `cos a` of the
length, and a plate at a right angle to the light blocks it.

Two tricks made very deep networks trainable: skip connections and
normalisation (**recalled**: He et al. 2016; Ioffe and Szegedy 2015; Ba, Kiros
and Hinton 2016). What are they, as optics?

Here a plate is written for light of any number of dimensions, so the same
statements hold for a flock of activations of any width.

## A skip connection is a bypass

A skip connection adds a layer's input to its output. In optics: split the
beam, send one part through the plate and one part around it, then join them.
Call this a plate with a bypass.

- **It never dims the light.** The squared length after a plate with a bypass
  is the squared length before, plus three times the squared shadow
  (**proved**: `norm_skipPlate_sq`, `norm_le_norm_skipPlate`). A bare plate
  can only lose length. A plate with a bypass can only gain it.
- **A crossed plate does nothing.** A bare plate at a right angle kills the
  light. With a bypass the light passes unchanged
  (**proved**: `plate_of_crossed`, `skipPlate_of_crossed`). So the rule "dead
  stays dead" stops being a danger: no single layer can kill the signal.
- **It turns the light part of the way.** A bare plate snaps the light onto
  its axis. A plate with a bypass doubles the part of the light along the axis
  and leaves the rest as it was (**proved**: `inner_skipPlate`,
  `skipPlate_sub_plate`). So the light leans towards the axis without landing
  on it. The tangent of the angle left to turn is halved.
- **Many of them never quite arrive.** After `k` such plates with the same
  axis, the part along the axis has grown `2^k` times and the rest has not
  changed (**proved**: `inner_iterate_skipPlate`,
  `iterate_skipPlate_sub_plate`). The light gets closer to the axis at every
  plate and never reaches it. Each layer makes a small turn.

That last point is the wind tunnel again. A network with skip connections
turns its flock a little at each layer, which is the kind of path that loses
least (see `least-action.md`).

## Normalisation is an amplifier

Normalisation rescales a layer's output back to a standard size. In optics: an
amplifier after the plate that brings the light back to full brightness.

- **Full brightness after any turn short of a right angle.** If the light has
  any shadow at all on the plate's axis, then after the plate and the
  amplifier it lies along the axis at full strength
  (**proved**: `renorm_plate`, `norm_renorm_plate`).
- **So the loss is gone.** Send full-strength light through any number of
  plates, each turned less than a right angle from the last, with an amplifier
  after each. It comes out along the last axis at full strength
  (**proved**: `throughNormedPlates_eq`). Without amplifiers the length left
  is the product of the cosines. With them the size of each turn stops
  mattering.
- **It cannot raise the dead.** After a crossed plate there is nothing to
  amplify, and the output is still nothing
  (**proved**: `renorm_plate_of_crossed`).

So the two tricks fix different things. A bypass makes sure no plate can kill
the light. An amplifier makes sure light that survives does not fade. A
bypass alone lets the light grow without limit, and an amplifier alone is
helpless after a crossed plate. That may be why networks use both.

## What is not shown

- **Which normalisation.** Rescaling one example's activations to a standard
  length is closest to layer normalisation. Batch normalisation rescales each
  feature across a batch. That is a different operation, and it is not
  modelled here. **open**
- **ReLU.** A plate keeps the shadow on a line. A ReLU layer keeps the nearest
  point in a quadrant. The statements here are for plates.
- **Real optics.** Joining two beams and amplifying light both have costs that
  the picture leaves out. This is a picture of the arithmetic, not a design.
  **open**
- **Training.** Nothing here is about how these tricks change gradient
  descent. **open**
