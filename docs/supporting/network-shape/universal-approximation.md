# Universal approximation, and what it costs

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/Supporting/NetworkShape/UniversalApproximation.lean` unless another file is
named), **recalled**, or **open**.

## The idea

The universal approximation theorem says a network with one hidden layer can
come as close as you like to any continuous function, given enough neurons
(**recalled**: Cybenko 1989; Hornik 1991; Leshno et al. 1993). It is often
quoted as "a neural network can learn anything". It says less than that. It
says a good network exists. It does not say how big it must be or whether
training finds it.

For ReLU networks on a line the proof is short, and it gives the size. The
size is the interesting part here, because it is set by slope.

## The construction

Take a function `f` on the interval from 0 to 1 whose slope is never more
than `K`. Cut the interval into `n` equal pieces. Build a network that agrees
with `f` at the ends of every piece and runs straight in between.

Each piece needs one "ramp": flat, then rising, then flat again. A ramp is
two ReLU units, one switching the rise on and one switching it off. So the
network has one hidden layer of `2n` units.

## The result

> A ReLU network with one hidden layer of `2n` units is within `2K / n` of
> `f` everywhere on the interval.

(**proved**: `relu_network_close`.) So for any error `ε` there is a network
that close (**proved**: `universal_approximation`). About `4K / ε` units are
enough.

The proof walks along the interval one piece at a time. Before a piece
starts, its ramp is flat at zero and changes nothing. After a piece ends, its
ramp is flat at its full height, and the network sits exactly on `f` at the
end of that piece. Inside a piece the network is a straight line between two
values of `f`, and `f` cannot stray far from either end, because its slope is
at most `K` (**proved**: `reluInterp_spec`).

## What it costs

The number of units goes as `K / ε`: slope over error.

That is the squiggly line story from the other side. A squigglier target is a
steeper one. To follow it with one hidden layer you pay in neurons, in
proportion to the slope. `depth-separation.md` showed the same price from
below: one neuron for every turn. Depth is how to avoid paying it, since each
layer can double the turns.

So the universal approximation theorem is true and is not the comfort it
sounds like. Anything can be drawn. The bill is the slope.

## What is not shown

- **Functions that are only continuous.** The proof is for a function with
  bounded slope. A continuous function on a closed interval can be handled
  the same way with a little more care (**recalled**), and that is not done
  here.
- **More than one input.** The construction is for one input. In many
  dimensions the count of pieces grows very fast (**recalled**).
- **Training.** That the network exists says nothing on whether gradient
  descent finds it. **open**
