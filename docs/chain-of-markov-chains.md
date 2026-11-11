# A chain of Markov chains

Notes from 11 Nov 2026, written before the proofs. Each statement is marked
**proved** (in `lean/`), **to prove**, or **recalled** (not derived here).

## What a Markov chain is

A Markov chain is a process with no memory. Where it goes next depends only on
where it is now, not on how it got there.

Training a deep network has this shape twice over. One chain runs through the
layers. Another runs through the training steps. Every step of the second runs
the first.

## The inner chain: through the layers

A bird's position after a layer depends only on its position before that
layer. Nothing earlier is kept. Every stack in this project works this way:

- the wind tunnel: each fan acts on what the last fan left;
- the polarizers: each plate acts on what the last plate passed;
- the folds: each fold acts on the previous output.

### The photon is a Markov chain in the full sense

For one photon there is real chance at every step. The photon is in one of two
states: **alive** or **absorbed**. At a plate turned by `θ` from the last:

- an alive photon stays alive with probability `c = cos² θ`, and is absorbed
  with probability `1 − c`;
- an absorbed photon stays absorbed.

So after `n` plates the probability of still being alive is `cⁿ`
(**to prove**). This is the square of the length we proved earlier,
`cos(θ)ⁿ`: brightness is length squared.

"Absorbed" is a state the chain never leaves. That is the photon's version of
a dead neuron.

### What having no memory costs

A chain with no memory can lose information and can never get it back. Three
facts we met separately are all this one fact.

- **Merged stays merged.** If two birds are at the same place after some
  layer, they are at the same place after every later layer (**to prove**).
- **The flock never spreads over more places.** Count the distinct places the
  flock occupies. That count can fall from layer to layer. It can never rise
  (**to prove**).
- **Dead stays dead.** If every layer leaves the dead state where it is, a
  bird that reaches it stays there (**to prove**). A blocked photon stays
  blocked, and a bird at the origin stays at the origin under any fan with no
  bias.

This is why depth is not free. Each layer is a chance to fold usefully and
also a chance to lose something for good.

## The outer chain: through training

The weights after a training step depend only on the weights before it. For a
model that is linear in its weights we proved the rule for the error:

```
error ← error − η · K · error
```

(**proved**: `residual_gradientStep`.) The next error depends only on the
current error. That is a chain with no memory.

When the features are orthogonal with squared length `c`, the kernel `K` just
multiplies by `c`, and the chain can be solved in closed form:

```
error after t steps = (1 − η·c)ᵗ × error at the start
```

(**to prove**.) Three things follow at once.

- With the step size `η = 1/c`, the factor is zero. **One step lands on a
  fit** (**to prove**). This is why the 513-parameter Fourier model trained in
  3 steps: its features are nearly orthogonal.
- With a smaller step the error shrinks by the same factor every step.
- With a step larger than `2/c` the factor is bigger than 1 in size and the
  error grows. That is training blowing up.

With random mini-batches the outer chain has real chance in it, like the
photon (**recalled**).

## One chain inside the other

Each training step does three things:

1. runs the inner chain forward, layer by layer, to get the outputs;
2. compares them with the labels to get the error;
3. runs the inner chain backward, layer by layer, to turn that error into a
   change of weights. This is backprop.

So the whole of training is a chain whose every link is itself a chain.

## Where the comparison is loose

- Most of these chains have no chance in them. The fans and folds are fixed
  rules, so the next state is certain. The randomness is in the weights, drawn
  once at the start, not in the steps. The photon and mini-batch training are
  the exceptions.
- A network with skip connections that reach back several layers does
  remember. Its inner chain is not memoryless.
- A full network trained in every layer does not obey the simple rule
  `error ← error − η·K·error`, because `K` itself changes as the weights move.

## What to prove

1. Merged stays merged, for any stack of layers.
2. The number of occupied places never rises.
3. Dead stays dead; in particular for a polarizer and for a fan.
4. The photon's two-state chain: after `n` plates it is alive with
   probability `cⁿ`, and absorbed is never left.
5. The closed form for the outer chain with orthogonal features, and the
   one-step fit at `η = 1/c`.
