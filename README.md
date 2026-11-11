# The Squiggly Line Conjecture

An idea from 2022 about why large neural networks learn fast, the experiments
that tested it, and a Lean formalisation of what turned out to be provable.

**Verdict:** the picture is geometrically true and does not explain learning.
A squigglier curve passes nearer to random points, but only in a distance that
training never measures.

- Write-up: [ad-absurdum.me/blog/squiggly-line-conjecture](https://ad-absurdum.me/blog/squiggly-line-conjecture)
- Slides: [2026 deck](https://docs.google.com/presentation/d/1xFoVq8pzuHHCICbLZh_NTZbHF80gQJMp8VbFF8Pzskc/edit?usp=sharing), [original deck](https://docs.google.com/presentation/d/1hucbKOalHq7g2sTdvyAnd1pDTRlAkg48H2wFui5UQTg/edit?usp=sharing)
- Full findings: [`docs/RESOLUTION.md`](docs/RESOLUTION.md)

## The idea

Scatter random points on a plane. Draw two curves without looking at the
points: one smooth, one squiggly. The squiggly one will pass closer to the
points on average, because it visits more of the plane.

A network computes a function, and the graph of that function is such a curve.
The conjecture said that a network with more parameters is a squigglier curve
at initialisation, so it starts closer to its data, so it learns faster.

That is three claims in a chain:

| # | Claim | Status |
|---|---|---|
| 1 | **Geometry.** A squigglier curve has a smaller mean distance to the nearest point of the curve. | True. Measured, and bounded by a theorem. |
| 2 | **Parameters.** More parameters give a squigglier random function. | False for width. Depth adds a little. |
| 3 | **Learning.** A smaller nearest-point distance means a smaller training loss at the start. | False. Proved. |

## Why it fails

The conjecture measures the distance from a data point `(x, y)` to the nearest
point of the curve. Regression measures the vertical error `|y − f(x)|`. These
are different, and four short results say how.

**1. The slope sandwich.** If `f` is `K`-Lipschitz, then at every data point

```
vertical / √(1 + K²)  ≤  nearest  ≤  vertical
```

The curve can be much nearer than its vertical error only if it is steep.
Squiggliness buys nearness with slope and with nothing else. A small
nearest-point distance means that a small change of the *input* reaches the
label, which describes a fragile function, not a well-fitted one.

**2. The marginal lemma.** The expected loss of a random function depends only
on the distribution of `f(x)` at each single `x`. How `f` moves between two
inputs, which is what "squiggly" means, does not enter. So no experiment on
the mean initial loss can detect squiggliness.

**3. The tube identity.** The mean distance from a random point to a set `S` is
the mass outside the tube of radius `r` around `S`, integrated over `r`:

```
E[dist(P, S)] = ∫₀^∞ P(P is outside the tube of radius r) dr
```

A tube around a curve of length `l` has area at most about `2·l·r`. So in a
region of area `V` the mean distance is at least about `V / (4·l)`, with
equality only when the curve is spread evenly. Length inside the data region
is necessary for coverage and is not sufficient.

**4. Width does not change the start.** Under He initialisation the second
moment of the output is the same at every width, so the expected initial MSE
is `E[y²] + E[f(x)²]` at every width.

Results 1 to 3 are proved in Lean (see [the formalisation](#the-formalisation)).
The bound in result 3 and result 4 are derivations checked by the scripts below.

## The evidence

### Frequency, with everything else held fixed

[`scripts/frequency_isolation.py`](scripts/frequency_isolation.py) uses sines
of one fixed amplitude and a random phase. Only the frequency changes.

| frequency | arc length | nearest-point distance | vertical error |
|---|---|---|---|
| 0.25 | 2.19 | 0.6129 | 0.6672 |
| 1 | 3.96 | 0.3095 | 0.6649 |
| 4 | 13.32 | 0.0928 | 0.6663 |
| 16 | 52.31 | 0.0338 | 0.6665 |
| 64 | 208.92 | 0.0207 | 0.6688 |

The nearest-point distance falls by a factor of 30. The vertical error does not
move. The second fact is the marginal lemma: a random phase gives `f(x)` the
same distribution at every frequency, so the column is flat by construction and
the small differences are sampling noise.

The distance stops falling at 0.0169 because the sine sweeps only the band
`|y| ≤ 0.816`, and points outside the band stay out of reach. With an amplitude
that covers the data there is no floor, and the distance follows
`0.2974 / frequency`. The constant is `(2 − 8/π²) / 4`, derived in
`docs/RESOLUTION.md` §6 and confirmed by
[`scripts/saturation_scaling.py`](scripts/saturation_scaling.py). Distance
times arc length tends to 1.19, a little above the 1.0 of an evenly spread
curve, because the strokes of a sine are not evenly spaced.

### A straight line of the same length

| frequency | arc length | sine | straight line, same length |
|---|---|---|---|
| 4 | 13.32 | 0.0928 | 0.5022 |
| 16 | 52.31 | 0.0338 | 0.5007 |
| 64 | 208.92 | 0.0207 | 0.5006 |

Read this table with care. A straight line of length 209 over `x ∈ [−1, 1]` has
slope 104, and about 99% of it lies above or below the data. So the table
shows that length outside the data region is worth nothing. It does not show
that length is irrelevant: by result 3, length inside the region is required.

### Random networks

[`scripts/initial_mse.py`](scripts/initial_mse.py): 10 inputs, 200 points, two
hidden layers, 200 untrained ReLU networks per width.

| width | 4 | 16 | 64 | 256 | 1024 |
|---|---|---|---|---|---|
| He initialisation, measured | 1.07 | 1.02 | 1.07 | 1.10 | 1.03 |
| He initialisation, predicted | 1.03 | 1.03 | 1.03 | 1.03 | 1.03 |
| Unscaled weights, measured | 15 | 220 | 3 450 | 60 200 | 823 000 |

A wider network does not start closer. With unscaled weights it starts much
further away, because the output grows with width. That growth is the
amplitude effect that made the first experiments in this repository look like
support for the idea.

[`scripts/random_relu_length.py`](scripts/random_relu_length.py) looks at the
curves themselves, for a 1-D input: width does not add arc length (3.4 to 3.6
from width 2 to 512), and depth adds some (3.4 to 5.1 from 1 to 16 layers).

## The formalisation

[`lean/`](lean) is a Lean 4 project on Mathlib. It states the conjecture and
proves the results above. There is no `sorry`, and each theorem depends only on
Lean's three standard axioms.

| File | Contents | Status |
|---|---|---|
| [`Defs`](lean/SquigglyLine/Defs.lean) | the curve, the data, the two costs | definitions |
| [`RandomFunction`](lean/SquigglyLine/RandomFunction.lean) | a randomly initialised model, its marginals, its expected cost | definitions |
| [`Conjecture`](lean/SquigglyLine/Conjecture.lean) | the conjecture and the learning claim | stated, not proved |
| [`Sandwich`](lean/SquigglyLine/Sandwich.lean) | `vertical / √(1 + K²) ≤ nearest ≤ vertical` | proved |
| [`Coverage`](lean/SquigglyLine/Coverage.lean) | the tube identity | proved |
| [`Marginal`](lean/SquigglyLine/Marginal.lean) | a regression loss sees only one-point marginals | proved |
| [`RandomPhase`](lean/SquigglyLine/RandomPhase.lean) | frequency does not change the marginals of a random-phase wave | proved |
| [`Verdict`](lean/SquigglyLine/Verdict.lean) | the learning claim fails for random-phase sines, for every regression loss and every data distribution | proved |

Both halves of the conjecture are one definition, `StartsCloser cost M μ`: the
expected cost falls strictly as the model grows. The conjecture uses the
nearest-point distance as the cost. The learning claim uses a regression loss.
`Verdict.lean` refutes the second for the sine family of the experiment:

```lean
theorem not_learningClaim_sineWave (A : ℝ) (hℓ : Measurable ℓ) (frequency : ℕ → ℝ)
    (μ : Measure (DataPoint ℝ)) : ¬ LearningClaim ℓ (fun m => sineWave A (frequency m)) μ
```

Not formalised: that frequency lowers the nearest-point distance (measured
only), the bound `V / (4·l)`, and the statements about network width.

To build (the first build downloads Mathlib):

```bash
cd lean
lake exe cache get
lake build
```

The files were checked with Lean 4.36.0-rc1 against the Mathlib commit pinned
in [`lean/lakefile.toml`](lean/lakefile.toml).

## Running the experiments

```bash
pip install -r requirements.txt
cd scripts

python frequency_isolation.py    # the main experiment, ~10 s
python saturation_scaling.py     # what sets the floor, several minutes
python initial_mse.py            # random networks at five widths, ~1 min
python random_relu_length.py     # arc length of random ReLU curves
python audit_legacy_metrics.py   # reproduces the defects listed below
```

## Repository layout

| Path | Contents |
|---|---|
| `docs/RESOLUTION.md` | the findings in full |
| `docs/EXPERIMENT_LOG.md` | a re-run of every script, 19 Sep 2026, with raw output |
| `docs/literature-survey.md` | related work |
| `docs/` (other) | development notes, kept as history |
| `lean/` | the formalisation |
| `scripts/curves.py` | shared sine-curve geometry, with an exact point-to-curve distance |
| `scripts/` (experiments) | the five scripts above |
| `scripts/` (other) | the first exploratory code, kept as a record |
| `graphs/`, `diagrams/` | figures |
| `handoff.md` | open experiments, with a prediction and a stop rule for each |

## What went wrong the first time

The first scripts (August 2025) appeared to support the idea. Three of their
measurements were not what they claimed to be.
[`scripts/audit_legacy_metrics.py`](scripts/audit_legacy_metrics.py) reproduces
each one.

1. **The "distance" was a neuron count.** `utils.measure_coverage` compared the
   label with the number of active neurons, about half the width.
2. **The scaling law was the output fading.** `relu_chain.py` measured
   `‖net(x) − x‖`. Under Xavier initialisation the output shrinks as the width
   grows, so the value converged to `‖x‖`, the score of a network that returns
   nothing.
3. **The 1-D case measured against a diagonal.** One coordinate was used twice,
   which put every "random" point on the line `y = x`.

These scripts are kept unfixed, with a warning at the top of each, because the
audit depends on them. Do not cite their output.

Two later corrections were numerical. A fixed sampling grid overestimated
distances for steep curves (fixed 19 Sep 2026). The replacement still chose
the wrong stroke of the curve once the strokes were closer together than the
sample spacing, which overestimated one control by 11% at frequency 1000
(fixed 11 Nov 2026). Both are described in `docs/RESOLUTION.md` §2.

## Open questions

The original question is answered. What remains is in
[`handoff.md`](handoff.md):

- Does a larger network travel a shorter distance in weight space to reach a
  fit? Lazy-training theory says yes, so this would be a replication.
- The mean initial loss is flat in width. Is the chance of a low initial loss
  also flat?
- Does the best subnetwork of a random network improve with width where the
  full network does not?
- Where do the kinks of a ReLU network go during training?

One more direction came out of the formal work. The nearest-point distance
scores each point alone, so it cannot see whether a function fits many points
at once. The cost of a joint fit under a random-function prior with kernel `K`
is `yᵀK⁻¹y`. For random labels its mean is `tr K⁻¹`, which at fixed amplitude
is smallest when `K` is the identity, that is, for the least correlated and
squiggliest prior. For smooth targets the order reverses. This is untested
here beyond a quick numerical check.

## License

MIT. See [`LICENSE`](LICENSE).
