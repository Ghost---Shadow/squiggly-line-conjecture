# The Squiggly Line Conjecture

> **A Geometric Perspective on Neural Network Initialization**

> ### Status: resolved — see [`docs/RESOLUTION.md`](docs/RESOLUTION.md)
>
> The geometric claim holds. The learning claim does not. A squigglier curve
> really is closer to random data points, but only under a Euclidean
> nearest-point metric; under the vertical residual that a loss function
> actually charges, the effect is exactly zero. Several headline numbers in the
> earlier write-ups came from measurement code that was not computing what it
> claimed to. Details and reproductions below.

This repository contains the experiments and write-ups for an investigation into
whether randomly initialized complex functions begin training geometrically
closer to their data than simple ones. The investigation is finished. The answer
is a qualified no, and the qualification is the interesting part.

---

## What the conjecture said

Scatter random points on a plane and draw two curves without looking at them, one
simple and one squiggly. The squiggly curve will on average pass closer to the
points, because it covers more of the space. Extend this to neural networks and
you get a proposed explanation for why larger networks train faster: they start
closer.

## What is actually true

**Squiggliness does buy geometric proximity, and not through arc length.**

`scripts/frequency_isolation.py` holds amplitude exactly fixed and varies only
oscillation frequency, so the marginal distribution of `f(x)` is identical across
every curve tested. Euclidean minimum distance to random points falls 22× as
frequency rises, then saturates once the wavelength drops below the typical
inter-point spacing.

The fishing-line mechanism is wrong, though. A *straight line* stretched to the
same arc length (208 units, a near-vertical ramp) scores 0.501 against the wiggly
curve's 0.028 — eighteen times worse at identical length. Arc length is close to
irrelevant. What matters is that the length is spread across the domain rather
than spent in one place.

This incidentally answers the objection from Hanin, Jeong & Rolnick (ICLR 2022),
who show deep ReLU networks preserve expected curve length at initialization.
That would undercut the conjecture only if length were the mechanism. It isn't.

**Squiggliness buys nothing that training can use.**

In the same experiment, the mean vertical residual `|y_i - f(x_i)|` moves from
0.6686 to 0.6632 — under 1% — across a 100× change in arc length. Flat.

At every `x`, `f(x)` has the same marginal distribution regardless of frequency.
Wiggles let a curve pass near a point that is *horizontally displaced* from it.
Euclidean distance rewards that; MSE does not. The squiggly line is closer to the
data in a direction gradient descent cannot see.

Random ReLU networks confirm it directly. Initial MSE, 10 inputs, 200 random
points, before any training:

| width | 4 | 16 | 64 | 256 | 1024 |
|---|---|---|---|---|---|
| He init | 2.97 | 2.98 | 3.00 | 3.13 | 2.99 |
| unscaled | 20 | 83 | 312 | 1348 | 4884 |

Flat under standard init. Under unscaled init, width makes initial loss much
*worse* — the amplitude confound that inflated the early polynomial experiments.

## Known defects in the original code

Reproduce all three with `python scripts/audit_legacy_metrics.py`.

1. **`utils.measure_coverage` is not a distance.** It computes
   `abs(yi - np.sum(pattern))`, where `np.sum(pattern)` is the count of active
   neurons (≈ width/2). It rises from 4.9 at width 10 to 80.1 at width 160 —
   increasing with width, the opposite of the conjecture — while being reported
   as support for it. This metric underlies `coverage_measure.py` and
   `more_effects.py`.

2. **The `L ~ w^(-0.42)` scaling law is signal attenuation.** `relu_chain.py`
   measures `||net(x) - x||`. Under Xavier init the input layer's variance scales
   as `2/(2+w)`, so the network output decays toward zero as width grows and the
   metric converges to `||x||` — the score of a network that outputs nothing
   (1.2325 at width 128 against a zero-function baseline of 1.2299).

3. **The 1-D branch measured against a diagonal.** `point[0]` is used for both
   coordinates, placing every "random data point" on the line `y = x`.

## What survives

> For a curve of fixed amplitude and random phase on a bounded domain, expected
> minimum Euclidean distance to a random point falls with oscillation frequency
> and saturates once the wavelength drops below the typical inter-point spacing.
> Arc length is not the controlling variable; the distribution of that length
> across the domain is.

Correct, and a nicer statement than the one this started with. It just doesn't
explain why large networks train fast.

## Running things

```bash
pip install -r requirements.txt
cd scripts

python frequency_isolation.py    # the decisive experiment (numpy only, seconds)
python audit_legacy_metrics.py   # reproduces the three measurement defects
```

Legacy scripts (`coverage_measure.py`, `relu_chain.py`, `more_effects.py`,
`quantum.py`, `snake_relu.py`, `rnn_snake.py`, `transformer_snake.py`,
`hilbert.py`, `wind_tunnel.py`) are retained as a record. Their outputs should
not be cited — see the defects listed above, and
[`docs/EXPERIMENT_LOG.md`](docs/EXPERIMENT_LOG.md) for a full re-run.

A warning about those scripts: each ends with a `KEY FINDINGS` block assembled
from literal `print` statements that are not derived from anything computed
above them. In three cases they assert the opposite of what the script just
produced.

## Repository layout

| path | contents |
|---|---|
| `docs/RESOLUTION.md` | **the current findings** |
| `docs/EXPERIMENT_LOG.md` | full re-run of every script, 19 Sep 2026, with raw output |
| `docs/` (other) | development notes, kept as history |
| `scripts/frequency_isolation.py` | isolated-frequency experiment and arc-length null model |
| `scripts/audit_legacy_metrics.py` | demonstrations of the three measurement defects |
| `scripts/` (other) | original exploratory code |
| `main.tex`, `tex/` | draft paper, superseded and not maintained |
| `graphs/`, `diagrams/` | figures |

## Postscript

The conjecture was worth testing. The instinct to insist on measuring it rather
than accepting a handwave was the right instinct — it just needed the measurement
to be of the right thing. The negative result is cleaner than the positive one
would have been.

**📈 [Original presentation](https://docs.google.com/presentation/d/1hucbKOalHq7g2sTdvyAnd1pDTRlAkg48H2wFui5UQTg/edit?usp=sharing)** (predates the resolution)

## License

MIT — see `LICENSE`.
