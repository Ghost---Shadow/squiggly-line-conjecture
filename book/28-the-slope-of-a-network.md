# 28. The slope of a network

**In the repository:**
[`NetworkSlope.lean`](../lean/SquigglyLine/Supporting/NetworkShape/NetworkSlope.lean),
note [`network-slope.md`](../docs/supporting/network-shape/network-slope.md).
**You need:** chapters 3 and 14.

## The idea

Chapter 3 said a curve is near its data only by being steep. So the
first thing to ask of a network is how steep it can be. A network is a
stack of layers, and a stack is easy to measure: if you know how much
each layer can stretch a distance, you know how much the whole stack can.

Think of a photocopier chain. The first copier enlarges by 2, the second
reduces by half, the third enlarges by 3. Two points one centimetre
apart on the original end up at most `2 × 0.5 × 3 = 3` centimetres apart
on the last copy. The stretches multiply.

> A stack of layers is no steeper than the product of the slopes of its
> layers. The gradient coming back is held down by the same product.

## An example you can do by hand

A network has three layers with slopes at most 2, 0.5 and 3, and a
readout of slope at most 1. The product is `2 × 0.5 × 3 × 1 = 3`.

At a data point the vertical error is 1. By chapter 3 the nearest
distance is at least `1 / √(1 + 3²) = 1 / √10`, which is about 0.32. This
network cannot pass closer to that point than 0.32 unless its slope is
larger than 3.

Now use the same slope bound on a classifier. Its score at an input is
0.6. To make the score zero or negative, the input must move by at least
`0.6 / 3 = 0.2`. A smaller move cannot do it, because a move of size 0.2
changes the score by at most `3 × 0.2 = 0.6`.

Last, a linear model with three weights 2, −3 and 1. Add up their sizes:
`2 + 3 + 1 = 6`. Move each input by 0.05, in the direction of the sign of
its weight: up, down, up. The score changes by
`2 × 0.05 + (−3) × (−0.05) + 1 × 0.05 = 0.1 + 0.15 + 0.05 = 0.3`. That is
`0.05 × 6`. No nudge of at most 0.05 per input does more.

## The statement

```lean
/-- **A network is no steeper than the product of its layers.** -/
theorem lipschitzWith_runLayers
    {layers : LayerStack State}
    {slopes : List SlopeLimit}
    (each_layer_has_its_slope :
      List.Forall₂ (fun layer slope => LipschitzWith slope layer)
        layers slopes) :
    let network       := RUN_LAYERS layers
    let slope_product := slopes.prod  -- slopes multiply when functions are composed
    LipschitzWith slope_product network := by
```

*Read aloud:* if every layer in a list has its own slope limit, then
running all the layers one after another has a slope limit equal to the
product of those limits.

`RUN_LAYERS` feeds a state through a list of layers in order, as in
chapter 12. `List.Forall₂` says the list of layers and the list of
slopes match up one to one. `slopes.prod` is the product of the list.

```lean
/-- **Flipping a classifier takes a move of at least score over slope.** If the
score at `input` is positive and the score at `other_input` is not, then
`other_input` is at least `score / slope_limit` away. -/
theorem le_mul_dist_of_flip
    {Inputs : Type*} [PseudoMetricSpace Inputs]
    {model : Inputs → ℝ}
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit model)
    {input other_input : Inputs}
    (score_has_flipped : model other_input ≤ 0) :
    let score         := model input
    let allowed_score : ℝ := slope_limit * dist input other_input  -- the score cannot change faster than the slope
    score ≤ allowed_score := by
```

*Read aloud:* if a score of slope at most `slope_limit` has fallen to
zero or below at `other_input`, then the score at `input` was at most
`slope_limit` times the distance between the two inputs.

Dividing both sides by `slope_limit` gives the move of at least
`score / slope_limit`.

The rest of the file is named here. `lipschitzWith_relu` says a ReLU has
slope at most one. `lipschitzWith_activation_comp` says a layer made of
weights followed by such an activation is no steeper than the size of its
weights. `verticalDist_network_le` is the chapter 3 sandwich with the
product of slopes in place of the slope limit. `adjoint_comp_reverse`
says the transpose of a two-step map is the two transposes in reverse
order. `norm_adjoint_comp_le` says its size is at most the product of
the two sizes. `GET_LINEAR_SCORE` is the score of a linear model, and
`score_add_sign` and `abs_score_add_sub_le` are the nudge result of the
example. `softmax_le_softmax_iff` and `softmax_temperature_order` are
about temperature, and `sum_critic_gap_le` is about a critic of slope
one. Chapter 39 comes back to temperature.

## Why it is true

**The product.** The proof is by induction on the list of layers. With no
layers the network is the identity, which has slope one, and one is the
product of an empty list. With one more layer in front, the new network is
the old network after that layer. If the old network stretches by at most
`slope_product` and the new layer by at most its own slope, then the pair
stretches by at most their product. That is the rule for composing
slope limits, and it is all the proof uses.

**The ReLU.** `max input 0` changes by at most the input changes. The
weights change a distance by at most their size. So weights then ReLU
change it by at most the size of the weights.

**The flip.** The score changes by at most `slope_limit` times the
distance between the inputs. Going from `input` to `other_input` it
falls from `score` to at most zero, so it falls by at least `score`. So
`score` is at most `slope_limit × dist`.

**The way back.** Backpropagation sends the error through the layers in
reverse, each layer applying its transpose. Taking the transpose of a
two-step map swaps the order of the two steps. The size of a two-step map
is at most the product of the two sizes, and a map and its transpose
have the same size. So the gradient is held down by the same product as
the signal going forward.

**The nudge.** Each term of the score is a weight times an input. Moving
an input by the nudge in the direction of the sign of its weight adds the
size of the weight times the nudge. Any other nudge of the same limit adds
no more.

## What it explains

The product explains several habits. Weight decay shrinks every factor of
the product. Spectral normalisation holds every factor at one, which is
Miyato et al. 2018 (**recalled**); chapter 30 says more about it. The
best-known test-error bounds for deep networks are written in this
product (**recalled**: Bartlett, Foster and Telgarsky 2017). The proof
here is the product itself, not those bounds.

The flip result is the usual account of adversarial examples: a steep
classifier can be flipped by a small move. For a linear model the nudge
result makes it exact. With a thousand inputs and every weight of size
0.01, the sum of sizes is 10, so a nudge of 0.01 per input moves the score
by 0.1. Each input moved a little, and the total is large. That is the
account of why images can be changed invisibly (**recalled**: Goodfellow,
Shlens and Szegedy 2015).

The gradient result says slope and gradient share one fate. A product well
below one is a flat network and a vanishing gradient. A product well above
one is a squiggly network and an exploding gradient. Chapter 30 follows
that through depth.

## How this meets the squiggly line

This chapter is chapter 3 applied to a stack. The idea used is **slope**,
and the new fact is that slopes multiply when layers are stacked, which is
the first of the three answers of chapter 14. The fold of chapter 8 enters
through the ReLU, whose slope is at most one: a fold costs no slope, and
the slope of a network comes from its weights.

## What is not shown

- **That networks reach the bound.** The product of the sizes of the
  layers is an upper limit. A trained network is usually far less steep
  than it (**recalled**). How steep a random network is remains the main
  open problem.
- **Tightness of the adversarial bound** for networks that are not
  linear. For a linear model the nudge result is exact. For a stack of
  layers only the flip bound is proved.
- **That the best slope-one critic gives a distance between
  distributions.** Only the easy direction is proved.
- **Test-error bounds.** Recalled, not proved.

## Check yourself

1. Three layers have slope limits 0.5, 4 and 2. What slope limit does the
   stack have?
2. A classifier has slope at most 4 and a score of 2 at an input. How far
   must the input move to flip the score?
3. A linear model has 100 inputs and every weight has size 0.02. Each
   input is nudged by 0.01 in the worst direction. By how much does the
   score move?

**Answers.** (1) By `lipschitzWith_runLayers` the product, `0.5 × 4 × 2`,
which is 4. (2) By `le_mul_dist_of_flip`, `2 ≤ 4 × dist`, so at least
0.5. (3) By `score_add_sign`, the nudge times the sum of the sizes of the
weights: `0.01 × (100 × 0.02) = 0.01 × 2 = 0.02`. By `abs_score_add_sub_le`
no nudge of that size does more.

Previous: [27. Two players: the GAN game](27-two-players.md) · Next: [29. The distance field](29-the-distance-field.md)
