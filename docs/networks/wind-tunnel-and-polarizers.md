# The wind tunnel, in plain words

Notes from 11 Nov 2026. This is the picture behind the ReLU part of the
conjecture, written down before any of it was proved.

Each statement below is marked **proved** (in `lean/`), **checked** (by a
simulation or a calculation here), or **recalled** (from the literature, not
verified in this repository).

## The picture

Take a dense ReLU network. Feed it a batch of data points.

- **The birds** are the data points. At each layer every bird has a position:
  its vector of activations.
- **The fan** is one layer. It applies a linear map (rotate, stretch, shear,
  shift) and then ReLU.
- **The coops** are the outputs. A trained network lands black birds with black
  and white with white.

## The platonic path and three distances

The platonic path is the true rule from input to answer: for every possible
bird, where it should land. It always exists. It is fixed by the problem, not
by any network.

The network draws an approximation of it. Three different distances measure
how good that approximation is, and they behave differently:

| Distance | From | To | Depends on |
|---|---|---|---|
| Approximation error | the truth | the nearest thing this architecture can draw | the architecture |
| Training loss | the truth | what the network draws right now | the current weights |
| Travel | the current weights | the nearest weights that fit | the exchange rate |

The original conjecture was about the second distance at a random start. It is
false there (**proved**: `Marginal.lean`, `Verdict.lean`). It is true for the
third (**proved** for models linear in their parameters: `LinearModel.lean`,
`ExchangeRate.lean`; **checked** by `scripts/fourier_params.py`).

What the data fixes is where each bird takes off and where it must land. The
route through the hidden layers is not fixed: many routes land every bird
correctly. So the loss measures the landing.

## Backprop pays the Jacobian in instalments

The exact way to reach a fit is to take the full Jacobian `J` of the outputs
with respect to the weights and solve a system built from `J·Jᵀ`. That matrix
is the exchange rate between loss and travel.

Gradient descent never builds it. Backprop returns only `Jᵀ × residual`, at
the cost of one backward pass, and repeated small steps solve the same system
iteratively. With perfectly orthogonal features one step of the right size
lands on the nearest fit. That is why the 513-parameter Fourier model needed
3 steps (**checked**).

## Resolving power

A ReLU network can only draw straight pieces. Its resolution is the number of
pieces, like pixels. Each neuron is one fold.

- One layer of `n` neurons, one input: at most `n + 1` pieces.
- `L` layers of `n` neurons, one input: each layer folds what the earlier ones
  made, so the counts multiply. The maximum is about `n^L`.

The doubling is **proved** for two neurons per layer (`Depth.lean`): `L` such
layers draw a curve that alternates 0, 1, 0, 1 on `2^L + 1` evenly spaced
inputs, so it turns `2^L − 1` times. The general `n^L` bound is **recalled**.

So the maximum is width to the power of depth. Networks at a random start and
after ordinary training use about width times depth (**recalled**: Hanin and
Rolnick). The gap between the two is "possible but not practical".

The truth needs only finite resolution. A target whose slope never exceeds `K`
can be drawn to within `ε` with about `K / (2ε)` pieces.

100% accuracy is possible and not practical for two separate reasons. The
weights that produce `n^L` pieces are special and training rarely finds them.
And if the labels are noisy, no resolution gives 100% on new birds.

## One neuron per layer: a tunnel that cannot turn

```
relu(w1 · relu(w2 · relu(w3 · relu(w4·x + b4) + b3) + b2) + b1)
```

Every layer here is a monotone function of its input, and a chain of monotone
functions is monotone. So this network, at any depth, never turns: its output
only rises with `x`, or only falls (**proved**: `NarrowChain.lean`). Without
biases it is a single line through the origin, or dead.

## ReLU is a polarizer with a wide opening

A polarizer projects light onto one allowed direction. A ReLU layer projects
each bird onto an allowed region: the corner of space where every coordinate
is positive. In two dimensions that corner is a 90° wedge.

- A bird inside the wedge is untouched.
- A bird up to 90° outside it is pressed onto the nearest edge, and shortened
  by the cosine of the angle it was outside by. This is Malus's law.
- A bird in the opposite corner is blocked. The output is zero.

The weights decide how the wedge sits relative to the flock, just as one
chooses the angle of a polarizer.

All three cases are **proved** for a bird on the edge of the wedge
(`Polarizer.lean`), along with the fact that ReLU sends each point to the
nearest point of the wedge.

## The three-polarizer effect

Two polarizers at 90° block all light. A third at 45° between them lets light
through. The same happens here.

Ask one layer to turn a bird by 180° and it lands in the blocked corner. Turn
the wedge a little at each layer instead, and its trailing edge pushes the
bird along. Each step keeps the fraction `cos(step)`. For a full 180° turn in
`N` equal steps the surviving length is `cos(180°/N)^N` (**checked** by
simulation for 4, 8 and 16 layers):

| layers | surviving length |
|---|---|
| 2 | 0 |
| 3 | 0.125 |
| 4 | 0.25 |
| 8 | 0.53 |
| 16 | 0.73 |
| 64 | 0.93 |

The formula `cos(step)^N` is **proved**, and so is a floor: a half turn in
`N ≥ 3` steps keeps at least `1 − π²/(2N)`, which tends to 1.

More gradual means less loss. A simulation of 400 random two-neuron networks
per depth agrees: with small random angles every bird survives, and with
large ones only 2% are left after 16 layers (**checked**, not kept as a
script).

This explains the one-neuron tunnel. In one dimension the only rotation is the
full 180° flip. There is no 45° to put in between. That is two crossed
polarizers with no room for a third.

## Where the analogy stops

- **Dragging flattens the flock.** The edge that pushes one bird pushes every
  bird it catches onto the same line. Their directions merge and only their
  lengths survive.
- **Turning everything is not the useful part.** Flipping the whole flock is a
  sign change, which the last layer does for free. A function turns when birds
  are treated differently: some inside the wedge and untouched, some outside
  and folded.
- **Light is linear and ReLU is not.** A polarizer acts the same way on every
  beam. The wedge leaves a quarter of all directions alone. That is why a
  stack of ReLU layers does not collapse into one linear map, and a stack of
  polarizers does.

## An optical network

The weights of a layer are a linear map, which optics does for free: printed
plates and interferometer meshes have been built as network layers
(**recalled**).

Printed polarizers give the weights and not the ReLU, because a stack of
polarizers is still one linear map. Two partial ways around it:

- A detector reads intensity, the square of the amplitude. That is one
  nonlinearity, at the last step only.
- Store a bird's position as a polarization angle. The light passing a
  polarizer goes as `cos²` of that angle, which is a nonlinear function of the
  stored value. One layer works. Chaining needs a material that turns
  brightness back into an angle, which takes high power (**recalled**).

Polarization is a two-dimensional state, so one beam is a layer of width 2.
