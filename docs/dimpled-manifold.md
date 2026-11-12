# The dimpled manifold, in the squiggly line picture

Notes from 12 Nov 2026. Written before the proofs, then updated once they were
done. Each statement is marked **proved** (in `lean/SquigglyLine/Supporting/NewInputs/Dimple.lean`),
**recalled** (from the paper, not checked against it line by line), or **open**.

## The hypothesis

Shamir, Melamed and BenShmuel, "The Dimpled Manifold Model of Adversarial
Examples in Machine Learning" (2021, arXiv:2106.10151). It was a large part of
the inspiration for the squiggly line idea.

Real data does not fill its space. Images, for instance, lie on a thin sheet
inside the enormous space of all possible pixel grids. Call the sheet the
data manifold.

The hypothesis is about where a trained classifier draws its boundary. It says
the boundary hugs the sheet: it runs almost along the data, and it dips a
little to one side or the other, in shallow dimples, to put each training
example on the correct side. An adversarial example is then a small step
straight off the sheet, across a dimple. The step is tiny because the boundary
was already right next to the data, and it looks like noise because it points
in a direction that no real data ever goes. (**recalled**)

## The same thing in our terms

Split an input into two parts: where it is **on** the sheet, and how far it is
**off** it. Real data always has "off" equal to zero.

Now take a function that is gentle along the sheet and steep across it:

```
f(position, height) = g(position) + K × height
```

Here `g` is what the function does on real data, and `K` is its slope in the
direction off the sheet.

Three things follow.

**1. Training cannot see `K`.** On real data the height is zero, so the
function equals `g`, whatever `K` is. Every loss on real data is the same for
every `K` (**proved**: `residualLoss_dimpled_onManifold`). Nothing in training rewards or punishes the slope
off the sheet.

**2. The adversarial step goes straight off the sheet, and its length is the
error divided by `K`.** Take a data point and any label you like. Step off the
sheet by `(label − g) / K` and the function gives exactly that label. The step
does not move along the sheet at all (**proved**: `dimpled_dimple`,
`dist_onManifold_dimple`, `dimple_fst`). So the nearest-point
distance of the squiggly line theorem is at most `vertical / K`.

**3. That is essentially the whole story.** If `g` has slope at most `L` along
the sheet, then no adversarial step can be shorter than
`vertical / √(1 + (L + K)²)` (**proved**: `nearestDist_dimpled_bounds`). For large
`K` the two bounds agree up to a constant: the adversarial distance is the
vertical error divided by `K`.

## What this adds to the squiggly line theorem

The theorem said: being close to the data has a price, and the price is slope.
That sounded like a function near the data must be a bad one.

The dimpled picture shows where the price can be paid: **off the sheet**. A
function can be gentle everywhere real data lives, so it behaves well on real
data, and still be steep in the directions real data never visits. It is then
within a hair of every data point in the nearest-point sense, which is exactly
what "has adversarial examples" means.

So two functions can agree on every real input, have the same loss on every
data set, and differ without limit in how fragile they are. The squiggly line
that hugs the data is the dimpled boundary.

This also answers an old question in this project: why does the nearest-point
distance matter if the loss cannot see it? Because it is the distance to the
nearest adversarial example.

## What is not shown

- **That training produces dimples.** The hypothesis says training first pulls
  the boundary onto the sheet and then dimples it. Nothing here is about what
  training does. Our statement is only that the loss leaves `K` free. **open**
- **Curved sheets.** The model has a flat sheet and one direction off it. The
  real claim is about curved, high-dimensional sheets. **open**
- **Why `K` ends up large.** Point 1 says training does not care. It does not
  say which `K` training picks. **open**
