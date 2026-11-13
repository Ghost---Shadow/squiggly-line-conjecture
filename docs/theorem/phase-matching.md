# Training can use the nearness, once the phase matches

Notes from 11 Nov 2026. This corrects a slogan used earlier in this project:
"a squigglier curve is closer to the data, in a direction training cannot
use". That was too strong. Each statement below is marked **proved** (in
`lean/`), **checked**, or **open**.

## What the nearest-point distance really measures

Take one data point and a curve that passes close to it, a little to the left
or right. The loss charges the vertical gap, which may be large. But slide the
curve sideways by the small distance to its nearest point, and the curve goes
through the data point. The loss for that point is then zero.

So the nearest-point distance is not a quantity that training cannot use. It
is the answer to a question about moving:

> How far must the curve slide sideways to hit this point?

For a sine, sliding sideways is a change of phase. Once the phase matches, the
point is fitted.

This puts the original picture in the same family as the parameter-space
result. Both are distances to move, not losses. The loss at the start does not
see either of them.

## One point: a shift

If the curve covers the labels within `ρ`, then for any single data point
there is a shift of the input, no larger than `ρ`, after which the curve
passes through the point (**proved**: this is what `COVERS_WITHIN` says).

For a sine of frequency `w` the shift is at most `π / w` (**proved**:
`sin_coversWithin`). In terms of the phase, the change needed is at most `π`,
half a turn, at every frequency (**proved**: `sin_exists_phaseShift`).

Those two numbers are worth comparing. Measured as a shift of the input, a
squigglier curve needs less movement. Measured as a change of phase, it needs
the same. A squigglier curve is more sensitive to its phase by exactly the
factor by which it is closer. This is the exchange rate again: the same
movement, in two units.

## Many points: a warp

One phase cannot match many points at once. Each point wants its own shift,
and the shifts differ. A single sine has one phase, so it can fit one point,
or two with luck.

What fits them all is a different small shift at each input: a warp of the
input axis. And here the covering bound gives everything at once.

> If the curve covers the labels within `ρ`, then any target at all with
> labels in range is fitted exactly, by the curve applied after a warp of the
> input that moves no point by more than `ρ`.

(**proved**: `exists_warp_of_coversWithin`; for sines,
`sineWave_exists_warp`, with `ρ = π / w`.)

So a squiggly enough curve can fit any data whatever, as long as something in
front of it may nudge each input a little. In a network that something exists:
it is the earlier layers. The last layers can be a fixed squiggly function,
and the first layers only have to learn a small warp.

## The price

Three costs come with a fit bought this way.

- **Slope.** The curve has to be steep to be that close (**proved**: the slope
  sandwich). A steep curve turns a small error in the warp into a large error
  in the output.
- **A rough warp.** The theorem promises a warp that moves no point far. It
  does not promise a smooth one. Neighbouring inputs with very different
  labels need very different shifts. The warp is gentle only when the curve
  wiggles many times between neighbouring data points.
- **Nothing between the points.** Away from the data the fitted function does
  whatever the squiggle does. This is memorising, not learning a rule.

## The corrected slogan

> A squigglier curve is closer to the data, in a direction the loss at the
> start cannot see. A small shift of the input cashes it in, at the price of
> slope.

The three claims, restated:

| Claim | Status |
|---|---|
| A squigglier curve is nearer to the data | true; **proved** for sines |
| That nearness is a lower loss at the start | false; **proved** for sines |
| That nearness is a short distance to a fit | true; **proved**: a warp of size at most the nearest-point scale fits any target |

## What is not shown

- **That gradient descent finds the warp.** The theorem says a small warp
  exists. Whether training reaches it, and how fast, is **open**. The loss as
  a function of one phase has many local minima at high frequency.
- **How smooth the warp can be.** A bound on its slope in terms of the
  frequency and the spacing of the data is **open**.
- **Networks.** That the early layers of a real network act as such a warp is
  a reading, not a result.
