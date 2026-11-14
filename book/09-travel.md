# 9. Travel

**In the repository:**
[`LinearModel.lean`](../lean/SquigglyLine/Networks/LinearModel.lean),
[`ExchangeRate.lean`](../lean/SquigglyLine/Networks/ExchangeRate.lean),
note [`fourier-parameters.md`](../docs/networks/fourier-parameters.md).
**You need:** chapters 1 and 5.

## The idea

Chapter 5 said a bigger model does not start with a lower loss. Chapters
4 and 7 said nearness is a distance to move. This chapter moves to the
place where that distance can be measured: the space of the weights.

Training moves the weights from where they start to somewhere that fits
the data. Call the distance from the start to the nearest weights that
fit every data point the **travel**. The claim of this chapter:

> A bigger model does not start lower. It starts **nearer to a fit**.

## The setting

The proofs are for a model that is **linear in its weights**: the vector
of its outputs on the data is a matrix times the weights. A Fourier
series is like this in its coefficients. A network is like this in its
last layer. In statistics this is plain linear regression on fixed
features.

| Name | Meaning | In Python |
|---|---|---|
| `predict weights` | the model's outputs on the data | `matrix @ weights` |
| `GET_RESIDUAL` | `labels - predict(weights)`: what is left to fit | |
| `GET_TRAVEL` | distance from the start to the nearest fit | |

## Three facts

**1. On the straight path to a fit, the error shrinks in proportion.**

```lean
theorem residual_along
    (end_weights_fit : predict end_weights = labels)
    (fraction : ℝ) :
    let weights_on_path    := MOVE_ALONG start_weights end_weights fraction
    let residual_on_path   := GET_RESIDUAL predict labels weights_on_path
    let residual_at_start  := GET_RESIDUAL predict labels start_weights
    let remaining_fraction := 1 - fraction  -- the part of the path still ahead
    residual_on_path = remaining_fraction • residual_at_start := by
```

Half way along the path, half the error is gone. So the nearer the fit,
the more error a fixed amount of movement removes
(`exists_within_budget`).

**2. More weights never move the nearest fit further away**
(`travel_coprod_le`). A bigger model can always leave its new weights
alone and do what the smaller one did.

**3. The exchange rate.** Suppose that, seen from the data side, the
features are at right angles to each other and each has squared length
`squared_length`. The repository calls that `HAS_TIGHT_FEATURES`. Then
the travel is known exactly.

```lean
theorem travel_eq
    (features_are_tight : HAS_TIGHT_FEATURES predict squared_length)
    (squared_length_pos : 0 < squared_length)
    (labels : Outputs)
    (start_weights : Weights) :
    let linear_predict : LinearPredictor Weights Outputs := predict
    let travel        := GET_TRAVEL linear_predict labels start_weights
    let residual_size :=
      ‖GET_RESIDUAL linear_predict labels start_weights‖
    let exchange_rate := √squared_length  -- parameter distance per unit of residual, inverted
    travel = residual_size / exchange_rate := by
```

The error and the travel are one quantity in two units. Adding
parameters changes the rate between them.

## An example you can do by hand

One data point. The model has `m` features, and each equals 1 at that
point, so the prediction is the sum of the weights. The prediction is
off by 1.

The cheapest fix is to add `1 / m` to every weight. The length of that
move is `√(m × (1/m)²)`, which is `1 / √m`. Here `squared_length` is `m`,
and the theorem says the same: travel is `1 / √m`.

With 4 features the travel is 0.5. With 100 it is 0.1. The error at the
start was 1 both times.

## What the experiment shows

A Fourier series with random coefficients, scaled so the output has the
same spread at every size, fitted to 20 points with random labels.

| parameters | loss at start | travel to a fit | gradient-descent steps |
|---|---|---|---|
| 9 | 0.65 | no fit | never |
| 21 | 0.65 | 448 | 188 000 000 |
| 25 | 0.64 | 35.5 | 79 300 |
| 65 | 0.71 | 1.61 | 166 |
| 129 | 0.66 | 0.48 | 13 |
| 513 | 0.63 | 0.23 | 3 |

The loss at the start is flat, as chapter 5 says it must be. The travel
falls, and training time falls with it. For this model `squared_length`
is about the number of parameters, so the exchange rate predicts 0.45
and 0.22 for 129 and 513 parameters. Measured: 0.48 and 0.23.

The row with 21 parameters, just enough to fit 20 points, is the worst.
Chapter 10 comes back to it.

## What is not shown

- **The rate for real features.** The exact formula needs tight features.
  That the Fourier model is nearly tight is measured, not proved.
- **Models that are not linear in their weights.** A deep network's
  features move during training. Then the travel is not a straight line
  and none of this applies as stated.

## Check yourself

1. You are 30% of the way along the straight path to a fit. How much of
   the error is left?
2. The features are tight with `squared_length = 25` and the error at the
   start has size 2. What is the travel?
3. A colleague says: "The bigger model trains faster because it starts
   with a lower loss." What do you answer?

**Answers.** (1) 70%. (2) `2 / √25`, which is 0.4. (3) It starts with the
same loss. It trains faster because a fit is nearer in weight space.

Previous: [8. Folds](08-folds.md) · Next: [10. The kernel](10-the-kernel.md)
