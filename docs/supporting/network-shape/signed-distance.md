# Signed distance functions

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/Supporting/NetworkShape/SignedDistance.lean` unless another file is
named), **argued**, **recalled**, or **open**.

## The idea

There are two ways to store a line.

- **As a height.** For each input `x`, the value `f(x)`. This is what a
  regression network learns.
- **As a field.** For each point of space, the distance to the nearest point
  of the line, with a plus sign above the line and a minus sign below. This
  is a signed distance function. Networks that learn shapes this way are in
  wide use in graphics and 3D vision (**recalled**: Park et al. 2019,
  DeepSDF).

The theorem of this repository is about the distance from a data point to the
nearest point of the line. That distance is the field, read at the data
points (**proved**: `nearestDist_eq_distanceField`). So the project has been
about signed distance functions from the start, without the sign.

## The field is never steep

However squiggly the line is, its field changes by at most the distance
moved. Its slope is never more than one (**proved**:
`lipschitzWith_distanceField`).

The height can be as steep as you like. The field of the same line cannot.
The squiggle has moved from the size of the slope into the layout of the
field: where it is zero and where it has creases.

For a continuous line the field is zero exactly on the line (**proved**:
`distanceField_eq_zero_iff`). So the field stores the whole line and loses
nothing.

## Sphere tracing

To find where a ray meets a shape, graphics programs step along the ray. At
each point they read the field and step forward by that amount. The step is
safe: no point nearer than the field's value is on the line (**proved**:
`notMem_curve_of_dist_lt`). This is sphere tracing (**recalled**: Hart 1996).

## The sandwich, read as a statement about fields

The height above the line, `y − f(x)`, has the right sign and is zero on the
line. It is tempting to use it as a signed distance. The slope sandwich of
the theorem says how wrong that is.

```
|signed distance|  ≤  |height above the line|  ≤  √(1 + K²) × |signed distance|
```

for a line of slope at most `K` (**proved**: `abs_signedDist`,
`abs_signedDist_le_verticalDist`, `verticalDist_le_abs_signedDist`).

So the height overstates the distance, by at most the slope factor. Stepping
by the height would overshoot. Stepping by the height divided by `√(1 + K²)`
is safe again (**proved**: `notMem_curve_of_dist_lt_verticalDist_div`).
Dividing by a bound on the slope is the usual fix in sphere tracing
(**recalled**: Hart 1996).

## How this meets the squiggly line

- **The conjecture's loss is the mean size of the field at the data.** A
  squigglier line has a field that is small in more of space. That is the
  theorem.
- **The tube is a level set.** The tube of radius `r` round the line, used in
  `Coverage.lean`, is the region where the field is below `r` (**proved**:
  `distanceField_lt_iff_mem_thickening`).
- **Why a field can be easier to learn than a height.** Training learns
  gentle functions first (`docs/supporting/training/spectral-bias.md`). The
  height of a squiggly line is steep. Its field is not. (**argued**; the
  field has creases, which is a different kind of difficulty.)

## What is not shown

- **The slope is exactly one.** Away from the line and from its creases the
  field changes at rate exactly one in the direction away from the line.
  This is the eikonal equation. Only "at most one" is proved here. It is on
  `docs/wishlist.md`.
- **Closed shapes.** The line here is the graph of a function. A closed
  surface needs a different rule for the sign. The statements without a sign
  hold for any set.
- **That networks learn fields more easily.** Argued above, not measured
  here.
