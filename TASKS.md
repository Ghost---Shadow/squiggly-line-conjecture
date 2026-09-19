# TASKS

Work queue for the squiggly-line-conjecture repo, in priority order.
Context: [`docs/RESOLUTION.md`](docs/RESOLUTION.md) (findings),
[`docs/EXPERIMENT_LOG.md`](docs/EXPERIMENT_LOG.md) (full re-run, 19 Sep 2026).

Tasks 1–2 must happen before anything else. Tasks 3–8 are cleanup. Task 9 is
the only genuinely open scientific question left.

---

## 1. Commit the current working tree first

`README.md` is rewritten, `docs/RESOLUTION.md`, `docs/EXPERIMENT_LOG.md`,
`scripts/frequency_isolation.py`, `scripts/audit_legacy_metrics.py` are new, and
`scripts/quantum.py` + `requirements.txt` have one-line fixes. None of it is
committed. Do this before any deletion, so the replacement is in history before
the thing it replaces leaves the tree.

```bash
git add -A
git commit -m "Resolve conjecture: isolate frequency from amplitude, audit legacy metrics"
```

## 2. Remove the paper

```bash
git rm -r main.tex tex
git rm scripts/remove_unused_citations.py
git rm docs/section-3-detailed.md docs/section-4-detailed.md
git commit -m "Remove paper draft; superseded by docs/RESOLUTION.md"
```

Deliberately **not** in that list, decide separately:

- `docs/literature-survey.md` — paper-adjacent, but it is the only written record
  of the related work, and the Hanin result matters to the resolution. See task 6.
- `diagrams/` — conceptual illustrations (`core_idea_1..4`, `arc_length`,
  `the_wall`, `diminishing_returns`), not LaTeX figures. Several are still
  accurate and they are presumably what is in the slide deck.

## 3. Neutralize the hardcoded conclusion blocks

This is the highest-value cleanup. Every legacy script ends with a `KEY FINDINGS`
block of literal `print` statements not derived from anything computed. Three
contradict their own output (see `EXPERIMENT_LOG.md` §"Cross-cutting finding").

In each of `coverage_measure.py`, `relu_chain.py`, `more_effects.py`,
`quantum.py`, `hilbert.py`: **delete the `KEY FINDINGS` / `CONCLUSION` print
block entirely.** Do not try to rewrite it to match the data — these scripts
measure the wrong quantities, so no conclusion drawn from them is worth
printing. Leave the numeric output intact.

## 4. Add a defect header to each compromised script

Top-of-file docstring, so nobody reads a number out of these without warning.
Do **not** fix the underlying metrics — they are the historical record, and
silently correcting them destroys the evidence that the audit depends on.

- `utils.py` → note on `measure_coverage`: `dist = abs(yi - np.sum(pattern))`
  measures the count of active neurons (≈ width/2), not a distance.
- `coverage_measure.py`, `more_effects.py` → depend on the above.
- `relu_chain.py` → two defects: the `input_dim > 1` branch measures
  `||net(x) - x||` (signal attenuation under Xavier, converges to the zero
  function's score); the `input_dim == 1` branch uses `point[0]` for both
  coordinates, placing every point on `y = x`.
- `quantum.py` → coverage-by-energy peaks at the ground state, contradicting the
  α√E claim it was written to demonstrate.

Each header should point at `docs/RESOLUTION.md §4`.

## 5. Add a banner to the historical docs

`docs/day-1.md`, `day-2.md`, `day-2-quantum.md`, `consolidated.md`,
`complex-curves-have-lower-expected-distance.md`,
`submodular-distance-reduction-with-complexity.md`, `wind-tunnel-analogy.md`.

One blockquote at the top of each:

> **Historical.** Written before the conjecture was resolved. Empirical claims
> here are superseded by [`RESOLUTION.md`](RESOLUTION.md). Kept as a record of
> how the idea developed.

## 6. Fix the three verified citation errors in `docs/literature-survey.md`

If the file is kept:

- "Pennington and Ganguli" → **Pennington and Worah**, *Nonlinear random matrix
  theory for deep learning*, NIPS 2017.
- "Explaining neural scaling laws (PNAS 2024)" and "Bahri et al. (2024)" are the
  same paper, listed twice. Merge.
- Nagarajan & Kolter, distance from initialization — NeurIPS **workshop** paper
  (Deep Learning: Bridging Theory and Practice, 2017), not main track.

Also add, as the most relevant item and the one that was missing: Hanin, Jeong &
Rolnick, *Deep ReLU Networks Preserve Expected Length*, ICLR 2022 — with a note
that it does **not** undercut the result, because arc length turned out not to be
the mechanism (`RESOLUTION.md §2`).

Strip the "entirely original" / "unprecedented scope" language throughout.

## 7. Regenerate the current figure, drop the stale ones

```bash
cd scripts && python frequency_isolation.py
```

Produces `graphs/frequency_isolation.png`. Then `git rm` the figures that plot
the broken metrics — everything matching `graphs/coverage_*`, `graphs/relu_*`,
`graphs/more_effects_*`, `graphs/quantum_*`. Keep `graphs/wind_tunnel*` and the
`hilbert.py` outputs (`coverage_2d_comparison_*`, `coverage_metrics_*`) if you
want them; that experiment is sound even though its printed conclusion is not.

## 8. Try `snake_relu.py` once with torchvision installed

`pip install torchvision`, then run it. It was never executed in the re-run.
Determine whether it is (a) a real experiment worth auditing, (b) another
visualization like `rnn_snake.py`, or (c) dead. Record the answer in
`EXPERIMENT_LOG.md §8` and delete it if (c).

---

## 9. The one open experiment: saturation scaling

The surviving theorem says Euclidean coverage saturates once the wavelength drops
below the typical inter-point spacing. That makes a sharp, cheap, falsifiable
prediction that has never been tested.

For `n` points uniform on `[-1, 1]`, mean x-spacing is `2/n`. The curve
`f(x) = A√2·sin(wπx + φ)` has wavelength `2/w`. Saturation should therefore occur
at **`w* ∝ n`**.

Suggestive evidence already in hand: the existing run used `n = 30` and the knee
appears at `w ≈ 32`. That is close enough to be worth taking seriously and close
enough to be a coincidence.

Build `scripts/saturation_scaling.py`:

- reuse `euclid_distance`, `arclen`, `sine_curves` from `frequency_isolation.py`
  (factor them into a shared module rather than copy-pasting)
- sweep `n ∈ {10, 30, 100, 300, 1000}` × `w ∈ logspace(0, 3)`
- locate the knee per `n` — fit a two-segment power law, or take the `w` at which
  the marginal improvement drops below some fixed fraction. Define the criterion
  once and apply it uniformly; do not tune it per curve.
- regress `log w*` on `log n`. **Prediction: slope 1.0.**
- extend to `d` dimensions if the 1-D result holds: spacing goes as `n^(-1/d)`,
  so the prediction becomes `w* ∝ n^(1/d)`.

A slope near 1.0 closes the theorem. A slope that isn't means the saturation has
a different cause and the mechanism story needs another look. Either outcome is
worth having.

Write the result into `docs/RESOLUTION.md §6`, replacing the open-thread bullet.

---

## Not on this list

**Do not "fix" the legacy metrics.** Tempting, but they are the evidence for the
audit, and `audit_legacy_metrics.py` imports `utils.measure_coverage` directly —
correcting it silently breaks the demonstration and erases the record of how the
result went wrong. The defect headers in task 4 are the right treatment.

**Do not revive the quantum extension.** Beyond being circular (for a 1-D box
`E ∝ n²`, so `nodes ∝ √E` follows from the spectrum by change of variables), its
own script reports best coverage at the ground state, across a total spread of
14%. There is nothing there.
