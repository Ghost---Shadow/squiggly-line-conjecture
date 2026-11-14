# 7. The theorem for any function

**In the repository:**
[`Compression.lean`](../lean/SquigglyLine/Theorem/Compression.lean),
note [`general-theorem.md`](../docs/theorem/general-theorem.md).
**You need:** chapter 6.

## The idea

Look back at chapter 6 and ask what was special about the sine. The
answer is: nothing. All that was used is that raising the frequency
squeezes the curve sideways.

So take any model, of any number of inputs, and squeeze it:

```
squeezed_model(input) = model(squeeze_factor × input)
```

Every wiggle of the model becomes `squeeze_factor` times narrower. Three
things follow, and each is one line of reasoning.

- **Closer.** If the model covered the labels within `reach`, the squeezed
  one covers them within `reach / squeeze_factor`. The label you wanted
  is still there. It is just `squeeze_factor` times nearer.
- **Steeper.** If the model had slope at most `slope_limit`, the squeezed
  one has slope at most `squeeze_factor × slope_limit`. The same climb
  now happens over a shorter run.
- **No better.** If the output has the same distribution at every input,
  squeezing only changes which input is read. The marginals are the
  same, so by chapter 5 the expected loss is the same.

The sine is the special case of `sin` squeezed by its frequency, with
`reach = PI`.

## The statement

The squeeze is one line:

```lean
def COMPRESS (squeeze_factor : ℝ) (model : Model Inputs) : Model Inputs :=
  fun input => model (squeeze_factor • input)
```

The theorem, `squiggly_line_theorem_general`, has the same four claims as
the sine version, with `reach / squeeze_factor` in the place of
`PI / frequency`. Here is its first claim.

```lean
    -- Claim 1: the distance is squeezed between two bounds.
    let claim_1_distance_is_squeezed : Prop :=
      ∀ {squeeze_factor : ℝ}, 0 < squeeze_factor →
        ∀ (parameters : random_model.Param) (data_point : DataPoint Inputs),
          let squeezed_model :=
            (random_model.compress squeeze_factor).eval parameters
          let vertical_error   := GET_VERTICAL_ERROR squeezed_model data_point
          let nearest_distance := GET_NEAREST_DISTANCE squeezed_model data_point
          let slope_bound      := √(1 + (squeeze_factor * slope_limit) ^ 2)  -- Pythagoras: 1 across, squeeze_factor * slope_limit up
          let lower_bound      := vertical_error / slope_bound               -- a curve no steeper than that cannot pass any closer
          let upper_bound      := reach / squeeze_factor                     -- the covering distance, squeezed
          let label_is_in_range :=
            GET_LABEL data_point ∈ label_range
          let is_above_lower_bound := lower_bound ≤ nearest_distance
          let is_below_upper_bound := nearest_distance ≤ upper_bound
          label_is_in_range →
            is_above_lower_bound ∧ is_below_upper_bound
```

The givens of the theorem are the three things the argument needs: every
draw of the random model covers the labels within `reach`, no draw is
steeper than `slope_limit`, and the output has the same distribution at
every input (`HAS_HOMOGENEOUS_MARGINALS`).

## Why it is true

The three lemmas are the three bullets above.

| Fact | Lemma |
|---|---|
| closer | `COVERS_WITHIN.compress` |
| steeper | `lipschitzWith_compress` |
| no better | `marginal_compress_eq` |

Take "closer". The squeezed model at an input reads the old model at
`squeeze_factor × input`. The old model hits the wanted label somewhere
within `reach` of that. Divide that place by `squeeze_factor` and you
have an input of the squeezed model that hits the label, and it is within
`reach / squeeze_factor`.

After that the proof is chapter 6 again with new names.

## One dial, many names

The squeeze factor turns up all over deep learning under other names.
The proofs for the first three rows call this same file. Temperature is
the same trade, proved on its own.

| The dial | Where | Chapter |
|---|---|---|
| frequency of a sine | Fourier features | 6, 11 |
| one over the width of a bump | radial basis functions | 11 |
| stride of a convolution | reading every second position squeezes by two | 14 |
| one over the temperature | the slope of the scores of a softmax | 14, 15 |

Each time, the trade is the same: closer, steeper by the same factor, and
no better in loss.

## What is not shown

The theorem says what squeezing does. It does not say how squiggly a
network with **random** weights is to begin with, which is the `reach` of
such a network as it grows. That is the open half of claim 2 of chapter
1. See chapter 17.

## Check yourself

1. A model covers its labels within 2 and has slope at most 1. You
   squeeze it by 10. What are the new reach and slope limit?
2. For that squeezed model, a data point has vertical error 1. Between
   which two numbers does the nearest distance lie?
3. Why does "no better" need the same distribution at every input?

**Answers.** (1) Reach 0.2, slope limit 10. (2) Between `1 / √101`, about
0.1, and 0.2. (3) Squeezing changes which input is read at each place.
If the output's distribution differed from input to input, that could
change the marginals, and then chapter 5 would not apply.

Previous: [6. The theorem for sines](06-the-sine.md) · Next: [8. Folds](08-folds.md)
