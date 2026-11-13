> **Historical record, as of 10 November 2026.** This file is out of date. The current state of the project is in [`README.md`](README.md). Since this was written, the geometric claim has been proved for sines, with a named theorem in `lean/` (`squiggly_line_theorem`); the original idea turned out to be true in parameter space; and the straight-line test and the reading of Hanin, Jeong and Rolnick were corrected. Open work is now listed in [`docs/open-problems.md`](docs/open-problems.md).

# Handoff: 10 November 2026

For the person (or agent) who starts the next experiments in this repository.

## 1. Read this first

**The original conjecture is already resolved.** [`docs/RESOLUTION.md`](docs/RESOLUTION.md) (19 Sep 2026) is the current state:

- The geometric claim holds. A squigglier curve is nearer to random points in the Euclidean nearest-point distance.
- The learning claim is false. The vertical residual `|y - f(x)|`, which a regression loss charges, does not change with squiggliness. Initial MSE of random ReLU networks is flat in width under He initialisation.
- Arc length inside the data region is necessary and not sufficient. A straight line of the same length is 24 times worse, but about 99% of that line lies outside the data. How evenly the length is spread decides how much it buys.
- The saturation floor comes from amplitude against the data range, not from point spacing.

So "start the experiments" does not mean "test the conjecture". That is done. It means the open threads in section 4.

The clean-up tasks that were queued are complete.

## 2. What the November 2026 session produced

This work is outside the repository, except for one script.

| Item | Location |
|---|---|
| Slide deck (public) | https://docs.google.com/presentation/d/1xFoVq8pzuHHCICbLZh_NTZbHF80gQJMp8VbFF8Pzskc/edit?usp=sharing |
| Paper notes, 10 files | `C:\Users\soura\Desktop\Dump\digest\Overparameterization\` |
| Blog post (published 10 Nov 2026) | https://ad-absurdum.me/blog/squiggly-line-conjecture |
| Random ReLU length check | [`scripts/random_relu_length.py`](scripts/random_relu_length.py) |

**The session found this repository late.** The first version of the blog post was written from the owner's early notes only. After the owner approved it, the results of `RESOLUTION.md` were added (the blog section "What my experiments found"). The blog post is live at https://ad-absurdum.me/blog/squiggly-line-conjecture.

## 3. New findings from the session

### 3.1 Sign error in the original derivation

This is about the first derivation of diminishing returns in the early notes.

- The derivation uses `E[dist] ~ (1 - L*k*eps^(d-1)/V)^(1/d)` and says that the second derivative in `L` is positive.
- For `d > 1` the second derivative is negative. The factor `(1-d)/d^2` is negative, and `(1 - x)^(1/d - 2)` is positive. A negative exponent does not change the sign.
- So that formula gives increasing returns to length, the opposite of its conclusion. Checked numerically for d = 2, 3, 10.

### 3.2 The graph is a surface, not a curve

For an input dimension above 1, the graph of `f: [-1,1]^d -> R` is a d-dimensional surface. The integral `sqrt(1 + |grad f|^2)` is its area. The tube volume is then `area * 2*eps`, not `L*k*eps^(d-1)`. The curve formula is correct only for a 1-D path, for example a hidden-state trajectory.

### 3.3 Random ReLU networks do not get longer with width

`scripts/random_relu_length.py`, 1-D input, 300 networks for each size, no training, output rescaled to span the box.

| Sweep | Curve length | Turns | Euclidean distance |
|---|---|---|---|
| Width 2 to 512 (2 hidden layers) | 3.4 to 3.6, flat | 0.5 to 15 | 0.48 to 0.42, flat from width 16 |
| Depth 1 to 16 (width 64) | 3.4 to 5.1 | 3 to 36 | 0.44 to 0.34 |

- With the PyTorch default initialisation the curves are almost flat lines at all sizes (length 2.0 to 2.1).
- This agrees with the flat initial MSE in `README.md` and with Hanin, Jeong and Rolnick (2022).
- The script measures only the Euclidean distance. Read the caveats in its docstring before you cite it.

### 3.4 Literature, with a verdict against the conjecture

| Paper | Finding | Verdict |
|---|---|---|
| Raghu et al. 2017, arXiv 1606.05336 | Path length grows with depth when weights are large | For, depth only |
| Hanin, Jeong, Rolnick 2022, arXiv 2102.10492 | Expected length does not grow at He initialisation | Against the length mechanism |
| Dherin et al. 2021, arXiv 2111.15090 | SGD pushes arc length down | Against "longer is better" |
| Bubeck, Sellke 2021, arXiv 2105.12806 | More parameters allow a smoother fit | Against "parameters add squiggle" |
| Ramanujan et al. 2020, arXiv 1911.13299 | A wider random network holds a better subnetwork | For, after a search |
| Larsen et al. 2022, arXiv 2107.05802 | A random subspace of enough dimensions reaches the low-loss set | For, in weight space |
| Chiang et al. 2023 (ICLR) | Guess-and-check sampling generalises; wider is better | For size without training; the functions that fit are simple |
| Humayun et al. 2024, arXiv 2402.15555 | Kinks move away from the data during training | Against squiggle near the data |
| Hosseini, Fedorenko 2023, arXiv 2311.04930 | Trained language models straighten the token path | Against the squiggly token path |
| Martinelli, Brea, Gerstner 2026 | Width adds escape dimensions; lottery tickets do not explain it | Against the lottery-ticket link |

The notes in the digest folder give details. Most of their numbers come from automatic summaries of the papers and are not checked against the paper tables.

## 4. Open experiments, in priority order

Each one states a prediction and a stop rule before any run. This is the standard that `RESOLUTION.md` sets.

### E1. Reachability (the open thread of `RESOLUTION.md` section 6)

> Note (11 Nov 2026): addressed for models linear in their parameters, by `scripts/fourier_params.py` and the parameter-space proofs (`LinearModel.lean`, `ExchangeRate.lean`, `Kernel.lean`). Not addressed for ReLU networks; see `docs/open-problems.md` item 4.

- **Question:** does a larger network travel a shorter distance in weight space from initialisation to a fit?
- **Setup:** one fixed regression task (for example 200 points, 10 inputs, as in the README table). ReLU networks, widths 16 to 4096, He initialisation, one optimiser and one learning-rate rule fixed in advance. Train to a fixed MSE threshold.
- **Measure:** `||theta_T - theta_0|| / ||theta_0||`, steps to the threshold, and the change of the function on a held-out grid.
- **Prediction:** relative travel falls roughly as `1/sqrt(width)` (lazy-training results). This is known, so the result is a replication. Its value is that it states "starts closer" in the one space where it is true.
- **Stop rule:** if relative travel is flat in width at a fixed threshold, drop the reachability reading.

### E2. The lower tail, not the mean

- **Question:** the mean initial MSE is flat in width. Is the probability of a low initial loss also flat?
- **Setup:** sample many random networks for each width (He initialisation) on a small dataset. Estimate `P(MSE < tau)` for three values of `tau` fixed in advance.
- **Prediction:** flat. At large width the random function converges to a Gaussian process with a kernel that does not depend on width.
- **Stop rule:** if `log P` changes by less than the sampling error across widths, the "more tickets" reading fails for the full network. Then only a subnetwork search (E3) can save it.

### E3. Best subnetwork against the full network

- **Question:** does the best subnetwork of a random network get nearer to the data as width grows, in the vertical residual?
- **Setup:** the edge-popup algorithm of Ramanujan et al. on the E1 task. Keep the number of kept weights constant across widths.
- **Measure:** vertical MSE of the best subnetwork, and of the full random network as the control.
- **Prediction:** the subnetwork improves with width and the full network does not.
- **Stop rule:** none. Both results are informative.

### E4. Where the kinks go during training

- **Question:** does training keep, remove or move the squiggle?
- **Setup:** 1-D regression. Count the turns of `f` near the data points and far from them, at fixed training steps.
- **Prediction:** total length falls (Dherin et al.). Kinks leave the neighbourhood of the data late in training (Humayun et al.).
- **Stop rule:** none.

### E5. Geometry in d dimensions (low priority)

`RESOLUTION.md` section 6 did not run this, because it was conditional on a 1-D prediction that failed. Run it only if a pure geometry result is wanted. Use the surface area of the graph, not a curve length (section 3.2).

## 5. Rules of this repository that still apply

- Report the vertical residual next to every Euclidean distance.
- Hold amplitude fixed when you vary squiggliness. Polynomial degree and unscaled width change amplitude too.
- Fix every criterion before the run and apply it to all curves in the same way.
- No hardcoded conclusion blocks. Print only what the script computed.
- Do not fix the legacy metrics. They are the evidence for `scripts/audit_legacy_metrics.py`.
- Size the sample grid for the steepest slope, or use `scripts/curves.py`. A fixed grid overestimates distance for steep curves.
