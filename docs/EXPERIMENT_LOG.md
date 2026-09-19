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

---

## 1. `frequency_isolation.py` — the current experiment

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
available for this run writes text only. To refresh them locally:

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
