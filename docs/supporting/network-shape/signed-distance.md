# Signed distance functions

**Proofs:** [`Coverage.lean`](../../../lean/SquigglyLine/Theorem/Coverage.lean), [`Eikonal.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/Eikonal.lean), [`SignedDistance.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/SignedDistance.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/NetworkShape/SignedDistance.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/SignedDistance.lean) unless another file is
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

## On the way in, the slope is exactly one

Notes from 13 Nov 2026. Proofs in
[`lean/SquigglyLine/Supporting/NetworkShape/Eikonal.lean`](../../../lean/SquigglyLine/Supporting/NetworkShape/Eikonal.lean).

"At most one" cannot be improved. Stand at any point of space, and walk in a
straight line toward a nearest point of the line. A fraction `t` of the way
there, the field is the fraction `1 - t` of what it was (**proved**:
`infDist_toward_nearest`, and `distanceField_toward_nearest` for the
squiggly line). So the field falls by exactly the distance walked
(**proved**: `infDist_sub_infDist_toward_nearest`).

Two things follow.

- **No smaller slope limit holds.** If any point off the set has a nearest
  point in it, the field has no slope limit below one (**proved**:
  `not_lipschitzWith_infDist_of_lt_one`).
- **A sphere-tracing step is as long as it can be.** A step of the full
  field value, taken toward the nearest point, lands on the line. A longer
  safe step does not exist.

A nearest point exists for every point when the set is closed and the space
is one where closed balls are compact, such as the plane (**proved**:
`exists_nearest_with_unit_rate`).

This is the part of the eikonal equation that needs no derivative. The
steepness of the line does not enter: the field of a very squiggly line and
the field of a flat one both fall at rate one.

## How this meets the squiggly line

- **The conjecture's loss is the mean size of the field at the data.** A
  squigglier line has a field that is small in more of space. That is the
  theorem.
- **The tube is a level set.** The tube of radius `r` round the line, used in
  [`Coverage.lean`](../../../lean/SquigglyLine/Theorem/Coverage.lean), is the region where the field is below `r` (**proved**:
  `distanceField_lt_iff_mem_thickening`).
- **Why a field can be easier to learn than a height.** Training learns
  gentle functions first (`docs/supporting/training/spectral-bias.md`). The
  height of a squiggly line is steep. Its field is not. (**argued**; the
  field has creases, which is a different kind of difficulty.)

## What is not shown

- **The eikonal equation as an equation.** The rate is exactly one along the
  straight path to a nearest point, and that is proved. That the field has a
  gradient of length one wherever it has a gradient at all is not stated in
  Lean.
- **Closed shapes.** The line here is the graph of a function. A closed
  surface needs a different rule for the sign. The statements without a sign
  hold for any set.
- **That networks learn fields more easily.** Argued above, not measured
  here.
