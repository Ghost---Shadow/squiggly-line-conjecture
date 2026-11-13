# Lottery tickets: what pruning costs

**Proofs:** [`LinearModel.lean`](../../../lean/SquigglyLine/Networks/LinearModel.lean), [`Pruning.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Pruning.lean).

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
[`lean/SquigglyLine/Supporting/NewInputs/Pruning.lean`](../../../lean/SquigglyLine/Supporting/NewInputs/Pruning.lean) unless another file is named), **recalled**,
or **open**.

## The idea

The lottery ticket hypothesis says a big network contains a small one that
could have been trained on its own, from the same starting weights, to do just
as well (**recalled**: Frankle and Carbin 2019). The small network is the
winning ticket. The other weights were never needed.

The squiggly line picture says more parameters put a fit nearer. Pruning takes
parameters away, so it should put the fit farther. Then how can a ticket win?

For a model that is linear in its weights both can be made exact.

## Kernels add

Split the weights of a model into the ones you keep and the ones you drop. Each
group has its own kernel. The kernel of the whole model is the sum of the two.
This is the standard rule for putting two sets of features side by side, and
it is taken as the meaning of "the whole model" here.

So pruning subtracts a kernel. Follow one direction of the labels. Say the kept
weights have strength `λ` there and the dropped weights have strength `μ`. The
whole model has strength `λ + μ` there (**proved**: `kernel_eigen_add`).

## What pruning costs

**It slows that direction down.** At each step the whole model multiplies its
error along that direction by `1 − η(λ + μ)`. The pruned model multiplies its
error by `1 − ηλ`. So at every step the pruned model has at least as large a
share of its error left (**proved**: `pruned_share_ge`). This is spectral bias
applied to the two kernels.

**It moves the fit farther.** Take the case where both groups of weights have
orthogonal features, of strengths `c` and `c'`. Then

```
travel of pruned model × √c  =  travel of whole model × √(c + c')
```

(**proved**: `travel_mul_sqrt_pruned`.) So pruning to a tenth of the strength
puts the fit `√10` times farther. This is the exchange rate read backwards.
The general statement, that adding parameters never moves the fit away, was
**proved** earlier (`travel_coprod_le` in [`LinearModel.lean`](../../../lean/SquigglyLine/Networks/LinearModel.lean)).

## When a ticket wins

A ticket wins on a direction when the dropped weights had no strength there:
`μ = 0`. Then the pruned model and the whole model keep exactly the same error
along that direction at every step (**proved**: `winning_ticket`).

So a winning ticket is not a small network that is as good in every way. It is
a small network that holds all the strength in the directions the labels
actually use. The dropped weights only had strength in directions the labels
never asked for.

That removes the puzzle. Pruning does cost, in general. It costs nothing when
what is cut was pointing somewhere the data never looks.

## What is not shown

- **That real networks contain such tickets.** This is the hypothesis. It is
  an observation about trained networks and is not derived here. **open**
- **Finding the ticket.** The usual way is to train, cut the smallest weights
  and rewind. Why small weights mark the unused directions is not shown.
  **open**
- **The starting function.** Dropping weights also changes what the model
  computes before training. Here the two models are compared from the same
  starting error.
- **Deep networks.** Kernels of a deep network do not simply add when weights
  are removed. **open**
