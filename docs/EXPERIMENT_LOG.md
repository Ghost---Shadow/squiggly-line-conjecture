# Experiment Log — full re-run, 19 September 2026

Every script in `scripts/` executed end to end on a clean environment
(numpy 2.4.4, torch 2.14.0+cpu, matplotlib/seaborn/pandas current). Raw stdout
recorded below. Read alongside [`RESOLUTION.md`](RESOLUTION.md).

**Summary of the re-run:** the two new scripts behave as documented. Of the nine
legacy scripts, two fail to execute, two are visualizations rather than tests,
and the remaining five produce output that contradicts the conclusions they
print.

---

## Cross-cutting finding: the conclusions are hardcoded

Every legacy script ends with a `KEY FINDINGS` block built from literal `print`
statements. Nothing in those blocks is derived from the numbers computed above
them, and in three scripts they assert the opposite of what the run produced.
This is the single most important thing to know before reading any historical
result in this repository.

| script | printed conclusion | what the run produced |
|---|---|---|
| `more_effects.py` | "Training reduces distance to test points, confirming the conjecture" | distance rose from 0.752 to 0.790 (−5.0% "reduction") |
| `quantum.py` | "Quantum networks show exponential advantage" | advantage = 1.00x at every qubit count, every dimension |
| `relu_chain.py` | "When all ReLUs fire positive, network = linear polynomial" | 87.5% fire in layer 2; discrepancy 2.54, not ~0 |

*Follow-up:* these blocks have since been deleted from `relu_chain.py`,
`more_effects.py`, `quantum.py` and `hilbert.py` (`coverage_measure.py` never
had one). The raw output below predates that change.

---

## 1. `frequency_isolation.py` — the current experiment

> **Superseded numerically — see [Addendum](#addendum--local-follow-up-19-sep-2026).**
> This run sampled curves on a fixed 4000-point grid, which overestimates
> Euclidean distance from frequency ≈32 upward. The plateau at 0.028 below is
> that artifact.

Runs clean. Amplitude fixed, frequency varied.

```
  freq   arc length    euclid dist   vert |resid|
--------------------------------------------------
  0.25         2.19         0.6142         0.6686
   0.5         2.66         0.4869         0.6639
     1         3.96         0.3105         0.6651
     2         6.96         0.1716         0.6665
     4        13.32         0.0929         0.6676
     8        26.26         0.0529         0.6667
    16        52.31         0.0346         0.6646
    32       104.49         0.0283         0.6638
    64       208.84         0.0279         0.6632

euclid: 0.6142 -> 0.0279   (22.0x improvement)
vert:   0.6686 -> 0.6632   (+0.8% change)

NULL MODEL: straight line stretched to identical arc length
  freq   arc length     wiggly   straight
     4        13.32     0.0929     0.5025
    16        52.31     0.0347     0.5007
    64       208.84     0.0279     0.5011
```

## 2. `audit_legacy_metrics.py`

Runs clean. Reproduces all three measurement defects; see `RESOLUTION.md` §4.

## 3. `coverage_measure.py`

Runs. Two things worth pulling out.

The headline metric tracks width/2 exactly, as predicted:

```
n=10:  avg_dist=4.990    n=80:  avg_dist=39.870
n=20:  avg_dist=10.020   n=160: avg_dist=80.178
n=40:  avg_dist=20.010
```

More interesting — section 3 of this script uses
`utils.measure_true_geometric_distance`, which is the *correct* Euclidean
metric, on actual ReLU networks:

```
Width 10: Geometric distance = 0.925
Width 20: Geometric distance = 1.085
Width 40: Geometric distance = 0.974
```

No trend with width. The one honest measurement already in this repository was
returning a null result the whole time. It was never plotted or discussed.

## 4. `more_effects.py`

Runs. This is where the "apparent dimension independence" in the old README came
from:

```
d=2, width=20: distance=10.323   d=4, width=20: distance=9.868
d=2, width=40: distance=19.956   d=4, width=40: distance=19.975
d=2, width=80: distance=39.686   d=4, width=80: distance=40.246
d=3, width=20: distance=10.179   d=5, width=20: distance=9.918
d=3, width=40: distance=20.181   d=5, width=40: distance=19.827
d=3, width=80: distance=39.127   d=5, width=80: distance=40.243
```

The quantity is `|y - (#active neurons)|` ≈ width/2. It does not depend on `d`
because it does not depend on the data at all. Dimension independence was the
absence of a measurement, not the presence of a pattern.

Training dynamics section:

```
Initial distance: 0.752
Final distance: 0.790
Distance reduction: -5.0%
```

Distance increased during training. The script then prints that training
confirms the conjecture.

Depth section shows a mild real decrease (1.079 → 0.855 over depths 1–4), but on
the same broken metric, so it carries no weight.

## 5. `relu_chain.py`

Runs (one deprecation warning on `x.T`). The all-positive-regime check does not
hold up: layer 2 has 87.5% of neurons firing, not 100%, so the network is not
the composite linear map it is claimed to equal — output `[-10.25, -14.34]`
against the linear computation's `[-11.58, -10.62]`, mean discrepancy 2.54.

The `w^(-α)` scaling law from this script is signal attenuation under Xavier
init; see `RESOLUTION.md` §4.

## 6. `hilbert.py`

Runs. This is the best-designed legacy experiment and it independently supports
the resolution's central point — that path length is not the mechanism.

2-D, Hilbert-initialized vs random network:

```
Path Length:   Hilbert 9334.94    Random 6834.16 ± 13.95    (+37%)
Avg Min Dist:  Hilbert 0.4847     Random 0.4968 ± 0.0129
               t = -2.324, p = 0.032  (n = 10)
```

3-D:

```
Path Length:    Hilbert 11161.02   Random 4500.28 ± 16.98   (2.5x)
Avg Min Dist:   Hilbert 0.4894     Random 0.5003
                t = -2.063, p = 0.054  -> not significant
Coverage Ratio: Hilbert 0.0547     Random 0.0881  -> Hilbert WORSE
```

A curve with 2.5× the path length buys a 2% distance change that does not reach
significance, and *loses* on coverage ratio. The script prints
"Hilbert initialization CONFIRMS better spatial coverage!".

## 7. `quantum.py`

**Fails on numpy ≥ 2.0**: `np.trapz` was removed. Patched locally to
`np.trapezoid` to obtain a run. (The same one-line fix has been applied in the
repo.)

Once running:

```
Dimension 2:  1..6 qubits: quantum advantage = 1.00x
Dimension 3:  1..6 qubits: quantum advantage = 1.00x
Dimension 4:  1..6 qubits: quantum advantage = 1.00x
```

Flat 1.00 everywhere. The script prints "exponential advantage in pattern
exploration" and "higher dimensions amplify quantum advantage further."

The coverage-by-energy section is the one that matters for the α√E claim:

```
Energy level n=1: coverage = 29.665
Energy level n=2: coverage = 27.313
Energy level n=3: coverage = 28.686
Energy level n=4: coverage = 25.920
Energy level n=5: coverage = 26.379
Best coverage at energy level 1
Coverage ratio (max/min) = 1.14
```

Non-monotonic, and the *ground state* wins. The quantum extension claimed higher
energy gives better coverage. Its own script says otherwise, across a total
spread of 14%.

## 8. `snake_relu.py`

**Fails to run**: `ModuleNotFoundError: No module named 'torchvision'`.
`torchvision` is imported at line 4 for MNIST and is absent from
`requirements.txt`. (Now added.)

*Follow-up run (torchvision 0.29.0):* it also needs `sklearn`, which was
missing from `requirements.txt` too (now added). On Windows it also needs
`PYTHONIOENCODING=utf-8`, because its emoji `print`s crash a cp1252 console.
With both fixed it runs to completion (~5 min on CPU). It trains a
784-512-256-128-64-10 MLP on MNIST for 3 epochs (97.59% test accuracy) and
renders the committed `flock_*` and `embedding_squiggle_*` figures.

**Verdict: (b), a visualization**, like `rnn_snake.py`. It traces how 1s and 5s
move through the layers of a *trained* network, and the only quantity it
computes is the distance between class centroids per layer. It measures
nothing about coverage or distance to data at initialization, so it neither
tests nor bears on the conjecture. Kept. Its closing "Observed flock behaviors"
lines are hardcoded like the other `KEY FINDINGS` blocks, but they make no
claim about the conjecture.

## 9. `rnn_snake.py`, `transformer_snake.py`

Both run clean. Neither tests the conjecture — they plot hidden-state
trajectories of untrained random networks through PCA and time axes. They are
illustrations of the metaphor, not measurements of it. No numbers to update.

## 10. `wind_tunnel.py`

Pure illustration, no experimental content.

---

## Figures

26 figures regenerate from the above. They were produced in a remote
environment and have **not** been copied back into `graphs/` — the connector
available for this run writes text only.

*Follow-up:* `graphs/frequency_isolation.png` and `graphs/saturation_scaling.png`
are now generated locally. The committed figures for the defective metrics
(`coverage_*`, `relu_*`, `more_effects_*`, `quantum_*`) have been removed from
`graphs/` and remain in git history. To refresh:

```bash
cd scripts
python frequency_isolation.py
python audit_legacy_metrics.py
```

The legacy scripts will also regenerate their figures, but those figures plot
the defective metrics documented above and should not be reintroduced into any
write-up.

---

## Environment

numpy 2.4.4 · torch 2.14.0+cpu · scipy 1.17.1 · matplotlib, seaborn, pandas
current as of 19 Sep 2026. `torchvision` was not installed; `snake_relu.py` was
not run.

---

## Addendum — local follow-up, 19 Sep 2026

Environment: numpy 2.5.1 · scipy 1.18.1 · torch 2.14.0 · torchvision 0.29.0,
Windows 11, Python 3.12.

### A. Grid-resolution artifact in `frequency_isolation.py`

At frequency `w` the sine's steepest slope is `A√2·wπ`, which is ≈164 at
`w = 64`. On the original fixed 4000-point grid, consecutive samples were
≈0.08 apart vertically there, larger than the distances being measured. Dense
sampling puts the high-frequency values well below the reported plateau:

| w | 4000-pt grid | dense (h = 0.002) |
|---|---|---|
| 16 | 0.0347 | 0.0344 |
| 32 | 0.0285 | 0.0252 |
| 64 | 0.0282 | 0.0212 |
| 128 | 0.0283 | 0.0192 |

The analytic limit as `w → ∞` is `(1 − A√2)²/2 = 0.0169`. The shared geometry
now lives in `scripts/curves.py`, which sizes the grid per frequency and refines
by segment projection. It matches a 10×-finer brute-force reference to 0.1% at
`w = 1000`. Straight-line distances are now computed exactly.

Corrected `frequency_isolation.py` output (≈10 s):

```
  freq   arc length    euclid dist   vert |resid|
--------------------------------------------------
  0.25         2.19         0.6129         0.6672
   0.5         2.66         0.4890         0.6664
     1         3.96         0.3095         0.6649
     2         6.96         0.1717         0.6651
     4        13.32         0.0928         0.6663
     8        26.26         0.0529         0.6678
    16        52.31         0.0338         0.6665
    32       104.50         0.0249         0.6657
    64       208.92         0.0207         0.6688

euclid: 0.6129 -> 0.0207   (29.6x improvement)
vert:   0.6672 -> 0.6688   (-0.2% change)
euclid limit as freq -> inf: 0.0169

NULL MODEL: straight line stretched to identical arc length
  freq   arc length     wiggly   straight
     4        13.32     0.0928     0.5022
    16        52.31     0.0338     0.5007
    64       208.92     0.0207     0.5006
```

All three conclusions stand, and the effect is larger than first reported.

### B. `saturation_scaling.py`

Tests the prediction that the knee sits at `w* ∝ n`. Runs in ≈4 min.

```
mean Euclidean distance D(w)
       w      n=10      n=30     n=100     n=300    n=1000
     1.0    0.3106    0.3097    0.3104    0.3098    0.3091
    10.0    0.0455    0.0450    0.0450    0.0454    0.0456
   100.0    0.0197    0.0193    0.0192    0.0195    0.0197
  1000.0    0.0175    0.0170    0.0170    0.0172    0.0175
     inf    0.0169    0.0169    0.0169    0.0169    0.0169
largest relative difference between any two n at any w: 3.1%

knee location w* per n
   criterion     n=10     n=30    n=100    n=300   n=1000    slope            95% CI
 two-segment     21.6     21.6     21.6     21.6     21.6   -0.000   [-0.004, 0.004]
    marginal     60.1     61.7     61.4     61.0     59.4   -0.003   [-0.014, 0.008]
prediction: slope 1.000

fit D - D_inf = c * w^-beta for w >= 20:  c = 0.236, beta = 0.978
if D = D_inf + c/w, the marginal knee is c(1-2r)/(2r D_inf) = 55.7, for every n

control: amplitude 0.707 (band |y| <= 1.000, covers the data), n = 100
  D(w=1) = 0.2962   D(w=100) = 0.00297   D(w=1000) = 0.00033
  tail fit: D = 0.285 * w^-0.989  (no floor)
  knees: two-segment 546.3, marginal none (every doubling still gains >= 10%)
```

The prediction is rejected: the knee does not depend on `n`. Saturation comes
from the band edge, not from point spacing. See `RESOLUTION.md §6`.

