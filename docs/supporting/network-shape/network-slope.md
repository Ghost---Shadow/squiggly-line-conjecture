# How steep a network can be, and what that slope costs

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in
`lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean` unless another file is
named), **argued**, **recalled**, or **open**.

## The idea

The theorem says a line is near the data only by being steep:
`vertical / √(1 + K²) ≤ nearest ≤ vertical`, where `K` is the slope. So the
slope of a network is the price of its nearness. This note collects the
places where that slope shows up under other names.

## The slope of a network is a product

A network is a stack of layers. If layer `i` stretches distances by at most
`Kᵢ`, the whole stack stretches them by at most the product of the `Kᵢ`
(**proved**: `lipschitzWith_runLayers`).

A ReLU has slope at most one (**proved**: `lipschitzWith_relu`). So a layer
"weights, then ReLU" is no steeper than the size of its weights (**proved**:
`lipschitzWith_activation_comp`), and

```
slope of the network  ≤  product of the sizes of the weight layers
```

The sandwich then reads in that product: a network can be nearer to a data
point than its vertical error only by the factor `√(1 + product²)`
(**proved**: `verticalDist_network_le`).

Two habits act on this product directly. Weight decay shrinks every factor.
Spectral normalisation holds every factor at one (**recalled**: Miyato et al.
2018). Both are limits on how squiggly the network may get. The product is
also what the best-known bounds on test error for deep networks are written
in (**recalled**: Bartlett, Foster and Telgarsky 2017).

## The gradient comes back through the same product

Backpropagation sends the error back through the layers in reverse, each
layer applying its transpose (**proved**: `adjoint_comp_reverse`). The size
of what comes back is bounded by the same product as the signal going forward
(**proved**: `norm_adjoint_comp_le`).

So slope and gradient share one fate. A product well below one is a flat
network and a vanishing gradient. A product well above one is a squiggly
network and an exploding gradient (`VanishingGradients.lean`).

## Adversarial examples

The boundary of a classifier is where its score is zero. How far is an input
from the boundary?

If the score has slope at most `K`, flipping the sign of a score `s` takes a
move of at least `s / K` (**proved**: `le_mul_dist_of_flip`). This is the
slope sandwich again, for a boundary in place of a line: a steep classifier
is one whose boundary passes near its data.

For a linear model the worst case is exact. Nudge every input by `ε`, each in
the direction of the sign of its weight. The score moves by `ε` times the sum
of the sizes of the weights, and no nudge of that size moves it more
(**proved**: `score_add_sign`, `abs_score_add_sub_le`). With a thousand
inputs the sum is large even when each weight is small. That is the usual
account of why images can be changed invisibly (**recalled**: Goodfellow,
Shlens and Szegedy 2015).

## Temperature

Dividing the scores by a temperature `T` divides their slope by `T`. It never
changes their order, so it never changes which answer is ranked first
(**proved**: `softmax_le_softmax_iff`, `softmax_temperature_order`).

So temperature is a way to change the slope of a classifier after training
without touching what it gets right. That is why it is used to repair
overconfidence (**recalled**: Guo et al. 2017). The overconfidence came from
cross-entropy asking for more slope without end
(`docs/supporting/training/cross-entropy.md`).

## A critic of slope one

One kind of generative model trains a critic to tell real samples from made
ones, and holds the critic to slope one (**recalled**: Arjovsky, Chintala and
Bottou 2017). Pair each real sample with a made one. The total gap such a
critic can report is at most the total distance between the pairs
(**proved**: `sum_critic_gap_le`).

So a slope-one critic measures how far the made samples are from the real
ones. It cannot say "infinitely wrong" about a sample that is nearly right.
The distance field of the real data is such a critic
(`lipschitzWith_distanceField` in `SignedDistance.lean`).

## What is not shown

- **That networks reach the bound.** The product of layer sizes is an upper
  limit. A trained network is usually far less steep than it
  (**recalled**). How steep a random network is remains the main open
  problem.
- **Tightness of the adversarial bound** for networks that are not linear.
- **That the best slope-one critic gives a distance between distributions.**
  Only the easy direction is proved.
- **Test-error bounds.** Recalled, not proved.
