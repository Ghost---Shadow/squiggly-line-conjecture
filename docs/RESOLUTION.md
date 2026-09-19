# Resolution of the Squiggly Line Conjecture

**Status: settled. The conjecture is true, and true in a direction that training cannot use.**

This document supersedes the empirical claims in `docs/day-1.md`,
`docs/day-2.md`, `docs/consolidated.md`, and the paper draft (`main.tex`, since
removed; see git history). The notes are kept as a record of how the idea
developed; they should not be cited for results.

---

## 1. The original claim

> Randomly initialized complex functions sit geometrically closer to random data
> points than simple ones, purely through increased spatial coverage. A larger
> network therefore begins training already closer to the data, which is why it
> learns faster.

Two separable parts: a **geometric claim** about curves and points, and a
**learning claim** that the geometry explains faster training.

---

## 2. The geometric claim is correct — and the stated mechanism is wrong

Earlier experiments varied squiggliness by raising polynomial degree or network
width. That confounds oscillation frequency with output amplitude and with arc
length, so it cannot say which one is doing the work.

`scripts/frequency_isolation.py` separates them. Curves are sines with amplitude
fixed at the standard deviation of the data and random phase, so the marginal
distribution of `f(x)` at any given `x` is *identical* across every row. Frequency
is the only variable.

| frequency | arc length | Euclidean min-distance | vertical residual |
|---|---|---|---|
| 0.25 | 2.19 | 0.6129 | 0.6672 |
| 1 | 3.96 | 0.3095 | 0.6649 |
| 4 | 13.32 | 0.0928 | 0.6663 |
| 16 | 52.31 | 0.0338 | 0.6665 |
| 64 | 208.92 | 0.0207 | 0.6688 |

Euclidean distance falls by a factor of 30. The effect is real, it is large, and
it is not an artifact of amplitude. **The squiggly curve is genuinely closer to
the data.**

But the fishing-line mechanism — more length, more chances to pass near a fish —
is not what produces it. Stretch a *straight line* to exactly the arc length of
each wiggly curve and it does not reproduce the effect:

| frequency | arc length | wiggly | straight, same length |
|---|---|---|---|
| 4 | 13.32 | 0.0928 | 0.5022 |
| 16 | 52.31 | 0.0338 | 0.5007 |
| 64 | 208.92 | 0.0207 | 0.5006 |

At 209 units of arc length the straight line is 24× worse. Length is nearly
irrelevant; what matters is that the length is **spread across the domain**
rather than spent climbing in one place.

This is worth stating plainly because it dissolves the strongest objection on the
table. Hanin, Jeong & Rolnick (ICLR 2022) show that deep ReLU networks preserve
expected curve length at initialization, which was taken to undercut the
conjecture. It doesn't, because length was never the operative variable.

*Numerical correction (19 Sep 2026).* The first version of these tables sampled
every curve on a fixed 4000-point grid. At frequency 64 the sine's steepest
slope is ≈164, so consecutive samples sat ≈0.08 apart vertically — larger than
the distances being measured — and Euclidean distance was overestimated from
frequency ≈32 upward (0.0279 reported at 64, 0.0207 true). The tables above use
`scripts/curves.py`, which sizes the grid per frequency and refines by segment
projection; it agrees with a 10×-finer brute-force reference to 0.1% at
frequency 1000. The straight-line column is now computed exactly. Every
conclusion stands and the effect is larger than first reported, but the
apparent plateau from frequency 32 onward was an artifact — see §5 and §6.

## 3. The learning claim is false

The same table already contains the refutation. The **vertical residual** — the
quantity a regression loss actually charges you — is flat: every value lies
between 0.6649 and 0.6688 across a 100× change in arc length. A 0.6% spread,
no trend.

The reason is simple. At every `x`, `f(x)` has the same marginal distribution no
matter how squiggly the curve is. Wiggles let the curve pass near a point that is
**horizontally displaced** from it. Euclidean distance rewards that; mean squared
error gives nothing for being near in `x` and charges the full vertical gap.

The squiggly line is closer to the data in a direction gradient descent does not
measure.

Direct confirmation on the object of interest — random ReLU networks, 10 inputs,
200 random points, initial MSE before any training:

| width | 4 | 16 | 64 | 256 | 1024 |
|---|---|---|---|---|---|
| He init | 2.97 | 2.98 | 3.00 | 3.13 | 2.99 |
| unscaled | 20 | 83 | 312 | 1348 | 4884 |

Flat under standard initialization. Under unscaled initialization width makes
initial loss dramatically *worse*, which is the amplitude confound that inflated
several of the early polynomial results (fixed coefficient range lets a degree-8
polynomial swing much wider than a degree-2 one).

## 4. Defects in the original measurement code

Run `scripts/audit_legacy_metrics.py` to reproduce all three.

**The core metric was not a distance.** `utils.measure_coverage`, used by
`coverage_measure.py` and `more_effects.py`, computes `abs(yi - np.sum(pattern))`
where `pattern` is the boolean activation vector. `np.sum(pattern)` is the *count
of active neurons*, roughly width/2. Measured output: 4.9 at width 10 rising to
80.1 at width 160. It increases linearly with width — the opposite of the
conjecture — while being captioned as support for it.

**The α ≈ 0.42 power law is signal attenuation.** `relu_chain.py` measures
`||net(x) - x||`, the distance from the network's output to its own input. With
Xavier init on a `2 -> w -> w -> 2` ReLU stack the input layer has `fan_in=2,
fan_out=w`, so weight variance scales as `2/(2+w)` and the output decays toward
zero as width grows. The metric therefore converges to `||x||` — the score of a
network that returns nothing. Measured: 1.3186 at width 2, 1.2325 at width 128,
against a zero-function baseline of 1.2299. The headline scaling law is the
network progressively going silent.

**The 1-D branch measured against a diagonal.** In `relu_chain.py`:

```python
dists = torch.sqrt((x_curve - point[0])**2 + (y_curve - point[0])**2)
```

`point[0]` supplies both coordinates, placing every "random point" on the line
`y = x`. The in-line comment flags it as a simplification; it is a bug.

## 5. What survives

A correct and modestly pretty result about random curves:

> For a curve of fixed amplitude and random phase on a bounded domain, expected
> minimum Euclidean distance to a random point falls with oscillation frequency
> as `D(w) ≈ D∞ + c/w`, saturating at a floor `D∞` set by amplitude: points
> outside the band the curve sweeps can never be reached. The floor and the knee
> do not depend on how many points there are. Arc length is not the controlling
> variable; distribution of that length across the domain is.

For the amplitude used here the band is `|y| ≤ 0.816` and the floor is
`(1 − 0.816)²/2 = 0.0169`. The original write-up anticipated saturation from the
curve "wasting its length by looping back on itself". That is not what happens.
The curve keeps closing in on every point inside its band at rate `1/w`, and
what remains is the fixed cost of the points outside it (§6).

What does not survive is the bridge to learning. The metric that makes the
theorem true is not the metric that training minimizes.

## 6. Open threads, if anyone wants them

- **Saturation scaling — tested, prediction rejected.** The claim was that
  saturation sets in once the wavelength `2/w` drops below the mean inter-point
  spacing `2/n`, so the knee should sit at `w* ∝ n` (slope 1.0 of `log w*` on
  `log n`). `scripts/saturation_scaling.py` sweeps `n ∈ {10, 30, 100, 300, 1000}`
  × 25 frequencies in `[1, 1000]`, 30 000 points per `n`, and locates the knee
  with two criteria fixed in advance and applied identically to every curve:

  | criterion | n=10 | 30 | 100 | 300 | 1000 | slope | 95% CI |
  |---|---|---|---|---|---|---|---|
  | two-segment log-log fit | 21.6 | 21.6 | 21.6 | 21.6 | 21.6 | −0.000 | [−0.004, 0.004] |
  | doubling gains < 10% | 60.1 | 61.7 | 61.4 | 61.0 | 59.4 | −0.003 | [−0.014, 0.008] |

  **Slope 0, not 1.** The knee does not move across two decades of `n`, and the
  five `D(w)` curves agree to within 3.1% at every frequency. The data rule this
  out, and so does the metric's definition: the metric is a mean of per-point
  distances, so its expectation cannot depend on `n` at all. Inter-point
  spacing never enters.

  What sets the knee is the band edge. Fitting `D − D∞ = c·w^(−β)` for `w ≥ 20`
  gives `β = 0.978` and `c = 0.236`. For `D = D∞ + c/w` the 10%-per-doubling
  knee is `c(1−2r)/(2r·D∞) = 55.7`, against 59–62 measured. As a control,
  widening the band to cover the data (`A√2 = 1`, so `D∞ = 0`) removes the
  saturation entirely. Distance falls as `0.285·w^(−0.989)` all the way to
  `w = 1000`, reaching 0.00033, and the 10% criterion never triggers. (The
  two-segment fit still reports a breakpoint, at 546, because it always
  returns one. The marginal criterion is the one that can say "no knee".)

  The "knee at `w ≈ 32` for `n = 30`" that suggested this test was the
  grid-resolution artifact described in §2.

  The saturation story needs the correction made in §5: amplitude against data
  range, not point spacing. The `d`-dimensional extension (`w* ∝ n^(1/d)`) was
  conditional on the 1-D result holding, so it was not run.

  ![saturation scaling](../graphs/saturation_scaling.png)
- Does the coverage result say anything about *reachability* — how far parameters
  must travel from initialization — rather than initial loss? That is a different
  and still-open question, and closer to what the lottery-ticket literature is
  actually about.
- The quantum appendix (`scripts/quantum.py`, `docs/day-2-quantum.md`) is
  probably circular: for a 1-D box `E ∝ n²`, so `nodes ∝ √E` follows from the
  spectrum by change of variables, and "coverage ∝ √E" follows from that. Worth
  checking before it is repeated anywhere.

---

*Experiments: `scripts/frequency_isolation.py` (≈10 s),
`scripts/saturation_scaling.py` (≈4 min), `scripts/audit_legacy_metrics.py`.
The first two share `scripts/curves.py` and need numpy + scipy.*
