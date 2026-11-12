# Chinchilla: how to split a compute budget

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/Supporting/Training/ComputeBudget.lean` unless another file is named),
**recalled**, or **open**.

## The idea

You have a fixed amount of compute. You can spend it on a bigger model or on
more training data. Which?

A study of large language models fitted their loss to a simple form and read
the answer off it (**recalled**: Hoffmann et al. 2022, known as the Chinchilla
paper):

```
loss  =  floor  +  A / (parameters ^ a)  +  B / (data ^ b)
```

The floor is what no model can beat. The second term falls as the model
grows, the third as the data grows. The fitted powers `a` and `b` came out
close to each other, about 0.34 and 0.28. Compute is roughly parameters times
data. The conclusion was that the two should grow together, and that earlier
models had been too big for the data they saw.

Two parts of this are reachable here: where the floor comes from, and why
"grow together" follows from the form. The form itself, and its powers, are
measurements and are not derived.

## The floor

The floor is the entropy of the data. No model's average log-loss can be
below it (**proved** earlier: `gibbs` in `CodeLength.lean`).

## The rule

Take the form with both powers equal to one: the loss above the floor is
`A / N + B / D`, with `N` parameters and `D` data, and the budget fixes
`N × D`.

**The best split balances the two terms.** If one split has
`A / N = B / D`, no other split with the same budget does better
(**proved**: `balanced_is_optimal`, and with the floor added,
`chinchilla_optimal`). The reason is the oldest inequality there is: for a
fixed product, a sum is smallest when its two parts are equal
(**proved**: `four_mul_div_le_sq`).

**At the best split, parameters and data are in a fixed ratio.** The ratio is
`N / D = A / B`, whatever the budget (**proved**: `balanced_ratio`).

**So they grow together.** Multiply both by the same factor and the split is
still balanced, for a budget that many times squared
(**proved**: `balanced_scale`). To use four times the compute, double the
model and double the data.

**What it buys.** At the best split the loss above the floor, squared, is
`4AB / budget` (**proved**: `balanced_loss_sq`). So the loss above the floor
falls as one over the square root of the budget.

**Any common power.** The same holds when both terms fall as the same power
of their size, whatever that power is (**proved**:
`balanced_is_optimal_rpow`). That covers the measured case to the extent that
0.34 and 0.28 are equal.

## Two rules, two situations

This rule and the rule of thumb for double descent look as if they disagree.

- **Fixed data.** You have a set of examples and cannot get more. The danger
  is the peak, where the model can just barely memorise them. Go well past
  it: about three parameters for each number to fit
  (`double-descent.md`, `capacity.md`).
- **Fixed compute, data to spare.** You can always get more data, and each
  example is seen about once. Then balance: grow the model and the data
  together. For language models the measured balance was about twenty tokens
  for each parameter (**recalled**), which is far fewer parameters than
  data.

They do not disagree. Both stay away from the peak, one from above and one
from below. With data to spare there is no reason to sit near the point where
the model is just big enough to memorise what it has seen.

## How this meets the squiggly line

The model term is the cost of a curve that cannot bend enough. For a function
of one input it falls as slope over the number of units
(`universal-approximation.md`). So `A` is a measure of how squiggly the
target is. A squigglier target has a larger `A`, and by the ratio `N / D =
A / B` it wants more parameters for each piece of data.

## What is not shown

- **Why loss has this form.** It is a fit to measurements. Here the model
  term is derived for one-input functions only, and the data term is not
  derived at all. **open**
- **The powers.** About 0.34 and 0.28 are measured. With unequal powers the
  best split balances the two terms in proportion to their powers
  (**recalled**), and that is not proved here.
- **Compute as parameters times data.** That is a fair count for one pass
  over the data with a model of fixed shape. It is an assumption.
