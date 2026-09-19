# Resolution of the Squiggly Line Conjecture

**Status: settled. The conjecture is true, and true in a direction that training cannot use.**

This document supersedes the empirical claims in `README.md`, `docs/day-1.md`,
`docs/day-2.md`, `docs/consolidated.md`, and `main.tex`. Those files are kept as a
record of how the idea developed; they should not be cited for results.

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
| 0.25 | 2.19 | 0.6142 | 0.6686 |
| 1 | 3.96 | 0.3105 | 0.6651 |
| 4 | 13.32 | 0.0929 | 0.6676 |
| 16 | 52.31 | 0.0346 | 0.6646 |
| 64 | 208.84 | 0.0279 | 0.6632 |

Euclidean distance falls by a factor of 22. The effect is real, it is large, and
it is not an artifact of amplitude. **The squiggly curve is genuinely closer to
the data.**

But the fishing-line mechanism — more length, more chances to pass near a fish —
is not what produces it. Stretch a *straight line* to exactly the arc length of
each wiggly curve and it does not reproduce the effect:

| frequency | arc length | wiggly | straight, same length |
|---|---|---|---|
| 4 | 13.32 | 0.0929 | 0.5025 |
| 16 | 52.31 | 0.0347 | 0.5007 |
| 64 | 208.84 | 0.0279 | 0.5011 |

At 208 units of arc length the straight line is 18× worse. Length is nearly
irrelevant; what matters is that the length is **spread across the domain**
rather than spent climbing in one place.

This is worth stating plainly because it dissolves the strongest objection on the
table. Hanin, Jeong & Rolnick (ICLR 2022) show that deep ReLU networks preserve
expected curve length at initialization, which was taken to undercut the
conjecture. It doesn't, because length was never the operative variable.

## 3. The learning claim is false

The same table already contains the refutation. The **vertical residual** — the
quantity a regression loss actually charges you — is flat: 0.6686 to 0.6632
across a 100× change in arc length. Under 1% drift, no trend.

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
> and saturates once the wavelength drops below the typical inter-point spacing.
> Arc length is not the controlling variable; distribution of that length across
> the domain is.

The saturation floor is visible from frequency 32 onward in the table above — the
"wasting its length by looping back on itself" regime anticipated in the original
write-up.

What does not survive is the bridge to learning. The metric that makes the
theorem true is not the metric that training minimizes.

## 6. Open threads, if anyone wants them

- The saturation frequency should go as `n^(1/d)` for `n` points in `d`
  dimensions. Untested here, cheap to test.
- Does the coverage result say anything about *reachability* — how far parameters
  must travel from initialization — rather than initial loss? That is a different
  and still-open question, and closer to what the lottery-ticket literature is
  actually about.
- The quantum appendix (`scripts/quantum.py`, `docs/day-2-quantum.md`) is
  probably circular: for a 1-D box `E ∝ n²`, so `nodes ∝ √E` follows from the
  spectrum by change of variables, and "coverage ∝ √E" follows from that. Worth
  checking before it is repeated anywhere.

---

*Experiments: `scripts/frequency_isolation.py`, `scripts/audit_legacy_metrics.py`.
Both are numpy-only and run in seconds.*
