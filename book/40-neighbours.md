# 40. Neighbours

**In the repository:**
[`Neighbours.lean`](../lean/SquigglyLine/Supporting/NewInputs/Neighbours.lean),
note [`neighbours.md`](../docs/supporting/new-inputs/neighbours.md).
**You need:** chapters 3, 4, 15 and 37.

## The idea

Three common methods use nothing but the distance between points.

- To label a new input, **copy the label of the nearest training
  input**. This is nearest neighbours.
- To group points, **put each point with its nearest centre**, then move
  each centre to the middle of its points, and repeat. This is k-means.
- To teach a model which pairs belong together, **score each pair by how
  close it is**. This is contrastive learning.

The theorem of this project is about the distance from the data to a
line. These methods use that distance directly. So they are the place
where the squiggly line meets everyday machine learning most plainly.

> Copying the nearest label is wrong by at most slope times distance.
> A k-means step never raises its cost. A contrastive score is a score by
> distance.

## An example you can do by hand

**Nearest neighbours.** The truth is `model(x) = 2x`, which has slope 2.
The training inputs are 1, 4 and 6, and the query is 3. The nearest
training input is 4, at distance 1. Copying its label says
`model(4) = 8`, but the truth at 3 is 6. The error is 2, and the bound is
`slope × distance = 2 × 1 = 2`. A line meets the bound exactly.

**k-means.** The points are 0, 2, 7 and 9, with two centres at 0 and 10.
Suppose the points 7 and 9 were both given the centre 0. The cost, the
sum of squared distances, is `0 + 4 + 49 + 81 = 134`. Give every point its
nearest centre: 7 and 9 move to the centre 10. The cost is
`0 + 4 + 9 + 1 = 14`. Now move each centre to the mean of its points. The
points 0 and 2 have mean 1, and the points 7 and 9 have mean 8. The cost
is `1 + 1 + 1 + 1 = 4`. The cost went 134, 14, 4. It did not rise.

**Contrastive scores.** Take two vectors of length one in the plane: the
query `(1, 0)` and the keys `(1, 0)` and `(0, 1)`. The dot products are
1 and 0. The squared distances are 0 and 2. Check the rule
`dot product = 1 − squared distance / 2`: `1 − 0 = 1`, and `1 − 1 = 0`.
At temperature 1, the softmax over dot products gives the first key
`e / (e + 1)`, about 0.731. The softmax over minus half the squared
distance has scores 0 and −1, and gives it `1 / (1 + e⁻¹)`, also about
0.731.

## The statement

```lean
/-- **Nearest neighbours.** If the truth `model` has slope at most
`slope_limit`, then copying the label of the nearest training input
`inputs nearest` is wrong by at most `slope_limit` times the distance from the
query to any training input, and so to the nearest. -/
theorem abs_sub_nearest_le
    {model : Model Space}
    {slope_limit : SlopeLimit}
    (slope_is_bounded : LipschitzWith slope_limit model)
    (query : Space)
    (inputs : Examples → Space)
    {nearest : Examples}
    (nearest_is_nearest :
      ∀ other, dist query (inputs nearest) ≤ dist query (inputs other))
    (other : Examples) :
    let copy_error := |model query - model (inputs nearest)|
    let bound      := slope_limit * dist query (inputs other)
    copy_error ≤ bound := by
```

*Read aloud:* if the truth has slope at most `slope_limit`, then the
error of copying the nearest training label is at most `slope_limit`
times the distance from the query to any training input.

`LipschitzWith slope_limit model` is the slope condition of chapter 3.
Taking `other` to be the nearest itself gives the tightest bound.

```lean
/-- **k-means, second half.** For the points of one cluster, no centre has a
lower cost than their mean. -/
theorem sum_sq_mean_le [Nonempty Examples]
    (points : Examples → Space)
    (other_centre : Space) :
    let mean :=
      GET_WEIGHTED_MEAN (fun _ => (Fintype.card Examples : ℝ)⁻¹) points  -- equal shares: 1 / count
    let mean_cost  := ∑ i, ‖points i - mean‖ ^ 2
    let other_cost := ∑ i, ‖points i - other_centre‖ ^ 2
    mean_cost ≤ other_cost := by
```

*Read aloud:* for the points of one cluster, the mean has a cost no
higher than any other centre.

`GET_WEIGHTED_MEAN` is the weighted average of chapter 37, here with
equal shares of one over the count. The double bars `‖ ‖` are length.

```lean
/-- **Contrastive learning scores by nearness.** For vectors of length one, the
softmax over cosine similarity at temperature `temperature` is the softmax over
minus the squared distance, divided by `2 * temperature`. -/
theorem softmax_cosine_eq_softmax_distance
    {query : Space}
    {keys : Examples → Space}
    (query_is_unit : ‖query‖ = 1)
    (keys_are_unit : ∀ i, ‖keys i‖ = 1)
    (temperature : ℝ) :
    let cosine_shares :=
      APPLY_SOFTMAX (fun i => inner ℝ query (keys i) / temperature)
    let distance_shares :=
      APPLY_SOFTMAX fun i => -‖query - keys i‖ ^ 2 / (2 * temperature)
    cosine_shares = distance_shares := by
```

*Read aloud:* for vectors of length one, the shares from a softmax over
dot products equal the shares from a softmax over minus squared distance
divided by twice the temperature.

`inner ℝ query (keys i)` is the dot product. For vectors of length one it
is the cosine similarity.

The other results of the file are named here. `sum_sq_reassign_le` is the
first half of a k-means step: moving every point to a no-further centre
does not raise the cost. `softmax_add_const` says adding the same number
to every score changes no share. `inner_eq_one_sub_of_unit` says that for
vectors of length one the dot product is one minus half the squared
distance.

## Why it is true

**Nearest neighbours.** The truth moves by at most slope times distance
between the query and the nearest input. That is the slope condition
used once. The nearest input is no further away than any other, so the
distance can be swapped for the distance to any training input.

**k-means.** The first half is a sum of squares. Each point's new
distance is no larger than its old one, so each square is no larger, and
so the sum is no larger (`sum_sq_reassign_le`). The second half is the
best-guess fact of chapter 37. The weighted mean is the best single
guess for a set of points under squared distance
(`weightedMean_isBest`). With equal shares the weights are one over the
count, a common factor on both sides, and the factor cancels.

**Contrastive.** Expand the squared distance between two vectors of
length one. It is `1 + 1` minus twice their dot product. Solve for the
dot product and you get `inner_eq_one_sub_of_unit`. So the dot product
and minus half the squared distance differ by the same constant for
every key. A softmax does not change when every score is shifted by one
constant (`softmax_add_const`). Dividing by the temperature then gives
the statement above.

## What it explains

**Nearest neighbours.** This is the theorem of the project read the other
way. Before, the nearness of a line to the data was bounded by the slope.
Here the error of a method is bounded by the distance to the data, times
the slope. It says how many training points you need: to halve the
bound, halve the distance to the nearest example.

**k-means and vector quantisation.** The cost never rises, so the method
cannot undo its own progress. Vector quantisation, the codebook layer of
chapter 39, is the first half of a k-means step used as a layer.

**Contrastive learning.** A contrastive loss scores pairs by nearness,
and its temperature is a width. The shares are those of the ideal
denoiser of chapter 37, with noise level the square root of the
temperature. So a contrastive loss at a low temperature is a hard
nearest-neighbour choice, and at a high temperature it is a broad
average.

## How this meets the squiggly line

Through **nearness** (chapter 4) and **slope** (chapter 3). The
nearest-neighbour bound is the slope sandwich used as a method: distance
to the data, times slope, is the error. The contrastive result adds
**averages** (chapter 15): a softmax over similarity is a softmax over
distance, so it is the same average as in chapter 37.

## What is not shown

- **That k-means stops.** Only that its cost never rises. That it
  settles on a final grouping is not shown.
- **What the contrastive loss does to the lift as it trains.** **open**
- **Nearest neighbours with noisy labels,** where the classical result
  compares its error with the best possible (**recalled**: Cover and
  Hart 1967).
- **Any model but the one the proofs use.** The truth has a known slope
  limit, the vectors have length one, and the cluster is fixed while its
  centre moves.

## Check yourself

1. The truth has slope at most 3. The nearest training input to a query
   is at distance 0.1. How wrong can the copied label be?
2. The points 1, 2 and 6 form one cluster. What is the mean, and is the
   cost at the centre 4 higher or lower?
3. Two keys are at squared distance 2 and 0.5 from a query, all of length
   one. By how much do their dot products with the query differ?

**Answers.** (1) At most `3 × 0.1 = 0.3` (`abs_sub_nearest_le`). (2) The
mean is 3. The cost at 3 is `4 + 1 + 9 = 14`. At 4 it is `9 + 4 + 4 = 17`,
which is higher, as `sum_sq_mean_le` says. (3) The dot products are
`1 − 2 / 2 = 0` and `1 − 0.5 / 2 = 0.75`, so they differ by 0.75
(`inner_eq_one_sub_of_unit`).

Previous: [39. Hard choices and temperature](39-hard-choices-and-temperature.md) · Next: [41. Counting](41-counting.md)
