# Three polarizers, and the photon's squiggly line

Notes from 11 Nov 2026, written before the proofs. Each statement is marked
**proved** (in `lean/`), **checked** (by a calculation here), **to prove**, or
**recalled** (textbook physics, not derived here).

## The experiment

A polarizer is a plate that lets through only the part of the light that
vibrates along one direction, its axis.

1. Put light through a polarizer with a horizontal axis. What comes out
   vibrates horizontally.
2. Put a second polarizer after it with a vertical axis. Nothing comes out.
   Horizontal light has no vertical part.
3. Now slide a third polarizer between the two, with its axis at 45°. Light
   comes out again.

Adding an obstacle lets more light through. That is the surprise.
(**recalled**)

## Why it happens

Each polarizer does one thing: it replaces the light's vibration by its shadow
on the polarizer's axis. If the axis is at an angle `θ` to the vibration, the
shadow has `cos θ` of the length. This is Malus's law. The brightness is the
square of the length, so it goes as `cos² θ`. (**recalled**; the shadow rule is
**to prove** as a statement about projections.)

- Horizontal light on a vertical axis: the angle is 90°, `cos 90° = 0`.
  Nothing passes.
- Horizontal light on a 45° axis: `cos 45° = 0.71` of the length passes, and
  it now vibrates at 45°.
- That 45° light on the vertical axis: the angle is 45° again, so another
  `0.71` passes.

`0.71 × 0.71 = 0.5` of the length, which is a quarter of the brightness. The
middle plate did not add light. It turned the light, so that the last plate no
longer saw it as fully crossed.

## The photon's path is a squiggly line

The photon flies straight through the plates. The line that squiggles is not
its route through the room. It is the route of its vibration.

Draw the vibration as an arrow on a sheet of paper: its direction is the
direction of vibration, its length is the strength. Each plate moves the tip
of the arrow to a new place. Join the places, plate after plate, and you have
a path on the paper. That path is the squiggly line.

- **Two plates, crossed.** The arrow points right, then drops to nothing. The
  path is one straight stroke into the origin.
- **Three plates.** The arrow points right, then at 45° and shorter, then
  straight up and shorter again. The path has a corner.
- **Many plates, each turned a little.** The arrow swings round in small
  steps, losing very little each time. The path is a chain of short strokes
  that hugs a quarter circle.

So the plates are layers, the arrow is the bird, and the path of its tip is
the bird's route through the wind tunnel.

## More plates, closer to the target

The target is the arrow pointing straight up at full length. Split the 90°
turn into `N` equal steps:

| plates after the first | length that arrives | brightness that arrives | length of the path |
|---|---|---|---|
| 1 | 0 | 0 | 1.00 |
| 2 | 0.50 | 0.25 | 1.21 |
| 3 | 0.65 | 0.42 | 1.31 |
| 5 | 0.78 | 0.61 | 1.40 |
| 10 | 0.88 | 0.78 | 1.48 |
| 30 | 0.96 | 0.92 | 1.54 |
| 90 | 0.986 | 0.973 | 1.56 |

(**checked**)

The length that arrives is `cos(90°/N)^N`. It is at least `1 − π²/(8N)`, so
the shortfall shrinks like one over the number of plates (**to prove**).

The path gets longer and squigglier as plates are added, and its far end gets
closer to the target. Its length climbs towards `π/2 = 1.571`, the length of
the quarter circle. The quarter circle is the platonic path: the turn with no
loss at all.

This is the one place in this whole project where the original conjecture is
simply true. A longer, squigglier path ends closer to the target, and the
distance falls at a known rate.

## One photon at a time

For a single photon the story is told differently and the numbers are the
same. Each plate is a measurement. The photon passes with probability
`cos² θ`, and if it passes, its vibration is now exactly along that plate's
axis. With many plates each turned a little, the photon almost always passes
every one, and is dragged round by being looked at often. Physicists call this
the quantum Zeno effect. (**recalled**)

## How this lines up with ReLU

| Polarizers | ReLU wind tunnel |
|---|---|
| a plate | a layer |
| the plate's axis | the positive corner of space, set by the weights |
| shadow on a line | nearest point of a wedge |
| loses `cos θ` per turn | loses `cos θ` per turn, for a bird on the edge |
| one 90° turn blocks | one turn past 90° blocks |
| many small turns pass | many small turns pass |

The ReLU side of this table is **proved** in `Polarizer.lean`.

One difference decides everything. A polarizer casts the shadow on a line, and
that is a linear operation. A whole stack of polarizers is one linear
operation and can compute nothing a single plate could not. ReLU casts the
shadow on a wedge, which leaves a quarter of all directions untouched and
folds the rest. That is not linear, and it is why depth adds something.

## What to prove

1. **Malus's law for the arrow.** A polarizer at angle `φ` sends an arrow of
   length `a` at angle `ψ` to an arrow of length `a·cos(φ − ψ)` at angle `φ`.
2. **Crossed plates block.** A plate at 90° to the arrow sends it to nothing.
3. **The chain.** After `k` plates, each turned by `θ` from the last, the
   arrow has length `a·cos(θ)^k` and angle `k·θ`.
4. **Three polarizers.** A plate at 45° and then one at 90° pass half the
   length, where the 90° plate alone passes none.
5. **More plates, closer.** For `N ≥ 2` plates the length that arrives is at
   least `1 − π²/(8N)`.
