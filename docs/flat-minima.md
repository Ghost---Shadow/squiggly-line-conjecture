# Flat minima: flatter is farther

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/Reparam.lean`), **recalled**, or **open**.

## The idea

There is an old belief that a network generalises well when training ends in a
flat place: a wide valley of the loss, not a narrow one (**recalled**:
Hochreiter and Schmidhuber 1997; Keskar et al. 2017). There is also a known
objection. You can rewrite the same network with rescaled parameters and make
any valley as narrow or as wide as you like, without changing a single output
(**recalled**: Dinh, Pascanu, Bengio and Bengio 2017, "Sharp Minima Can
Generalize For Deep Nets").

For a model that is linear in its weights both sides can be made exact, and
they fit together into one rule.

## Rescaling

Take a model and a number `c` that is not zero. Write a new model whose
parameters are `c` times the old ones, and which divides them by `c` before
using them. Nothing the model computes has changed.

- **Same outputs, same error.** The new model at `c × θ` gives what the old
  model gave at `θ` (**proved**: `rescale_smul`, `residual_rescale`).
- **Flatter by `c²`.** The loss curves less in every direction: its curvature
  is divided by `c²` (**proved**: `norm_rescale_sq`). So does the kernel
  (**proved**: `kernel_rescale`).
- **Farther by `|c|`.** The nearest fit is now `|c|` times as far from the start
  (**proved**: `travel_rescale`).

So a valley can be made ten times flatter. The price is that every fit moves
`√10` times farther away. Flatness on its own says nothing about the function.

## What does not change

Follow one direction of the labels, of strength `λ`. The strength is the
curvature of the loss there. Then

```
strength × travel²  =  error²
```

(**proved**: `strength_mul_travel_sq`.) The right side is the error at the
start, which rescaling does not touch. So flatness and distance are two
readings of one number. Flat means far. Sharp means near. Neither is better
before you say how the parameters are measured.

## Rescaling is a change of step size

Gradient descent is not blind to rescaling. One step of the rescaled model with
step size `η` is one step of the old model with step size `η / c²`
(**proved**: `gradientStep_rescale`). So "which valley does training find" and
"how flat is it" both depend on a choice of units. The only thing rescaling
changes about training is how fast it goes.

## How this meets the squiggly line

The squiggly line theorem measures steepness in data space: how fast the
output changes when the input changes. Rescaling the parameters leaves that
alone, because it leaves the function alone. This is the reason to measure
there. A statement about the steepness of the function is a statement about the
model. A statement about the flatness of the loss is partly a statement about
how the parameters were written down.

## What is not shown

- **Deep networks.** In a deep ReLU network one layer can be scaled up and the
  next scaled down. That is a rescaling of part of the parameters, not all of
  them. The rule here covers the whole-model case. **open**
- **Whether flat valleys generalise once units are fixed.** With a fixed way of
  measuring parameters the question is real again. It is not answered here.
  **open**
