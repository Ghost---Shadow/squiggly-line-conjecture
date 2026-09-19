"""
saturation_scaling.py

Tests the one open prediction left in docs/RESOLUTION.md: that Euclidean
coverage saturates once the curve's wavelength drops below the typical
inter-point spacing.

Prediction under test
---------------------
n points uniform on [-1, 1] have mean x-spacing 2/n. The curve
f(x) = A*sqrt(2)*sin(w*pi*x + phi) has wavelength 2/w. If spacing sets the
saturation, the knee sits at w* ~ n, i.e. slope 1.0 of log w* on log n.

Design
------
    - n in {10, 30, 100, 300, 1000}, w in logspace(0, 3, 25).
    - Every n gets the same point budget (POINT_BUDGET points split into
      POINT_BUDGET // n trials of n points), so all curves are estimated to
      the same precision. Within one n the same points are reused at every w
      (common random numbers), so the shape of each curve is not noise.
    - Each w uses a stratified pool of N_PHASES phases; trial t is scored
      against curve t % N_PHASES. The pool is shared across n.
    - Distances come from curves.py, which samples each curve finely enough
      to be accurate at w = 1000 (see the numerical note there).

Knee criteria, fixed once and applied identically to every curve
----------------------------------------------------------------
    two-segment : continuous two-piece linear fit of log D against log w,
                  breakpoint scanned over the interior of the w range, least
                  squares. w* = breakpoint.
    marginal    : w* = smallest w at which one doubling of w improves D by
                  less than MARGINAL_THRESHOLD (10%), interpolated in log w.

Uncertainty: bootstrap over trials within each n.

Mechanism check
---------------
The metric is a mean over points of each point's own distance to the curve,
so by linearity of expectation E[D] cannot depend on n at all. The alternative
explanation is the band edge: the curve sweeps |y| <= A*sqrt(2) = 0.816, so
points outside that band are unreachable and D(w) -> (1 - 0.816)^2 / 2 =
0.0169 as w -> infinity. That predicts D(w) ~ D_inf + c/w with a knee set by
c / D_inf -- independent of n -- and predicts that the saturation disappears
entirely when the band covers the data (A*sqrt(2) = 1). Both are checked.

Run:  python saturation_scaling.py      (numpy + scipy, ~4 minutes)
"""

import numpy as np

from curves import (AMPLITUDE, euclid_distance, floor_distance, peak,
                    phase_pool, sine_curve, sine_grid)

try:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    HAVE_PLT = True
except ImportError:
    HAVE_PLT = False

N_VALUES = [10, 30, 100, 300, 1000]
FREQUENCIES = np.logspace(0, 3, 25)
POINT_BUDGET = 30000
N_PHASES = 16
MARGINAL_THRESHOLD = 0.10
N_BOOTSTRAP = 300
TAIL_FROM = 20             # fit D - D_inf = c * w^-beta for w >= TAIL_FROM
CONTROL_AMPLITUDE = 1 / np.sqrt(2)   # band |y| <= 1 covers the data exactly
CONTROL_N = 100


# ---------------------------------------------------------------- measurement

def per_trial_distances(point_sets, amplitude, rng):
    """
    point_sets: {n: (px, py)} with arrays shaped (trials, n).
    Returns {n: array (trials, len(FREQUENCIES))} of per-trial mean distance.
    """
    out = {n: np.empty((px.shape[0], len(FREQUENCIES)))
           for n, (px, py) in point_sets.items()}
    for j, w in enumerate(FREQUENCIES):
        x = sine_grid(w, amplitude)
        for k, phi in enumerate(phase_pool(N_PHASES, rng)):
            y = sine_curve(w, phi, x, amplitude)
            for n, (px, py) in point_sets.items():
                rows = slice(k, None, N_PHASES)
                out[n][rows, j] = euclid_distance(x, y, px[rows], py[rows]).mean(axis=1)
    return out


def draw_points(n_values, rng):
    sets = {}
    for n in n_values:
        trials = max(POINT_BUDGET // n, N_PHASES)
        sets[n] = (rng.uniform(-1, 1, size=(trials, n)),
                   rng.uniform(-1, 1, size=(trials, n)))
    return sets


# ---------------------------------------------------------------- knee criteria

LOG_W = np.log(FREQUENCIES)
BREAKPOINTS = np.linspace(LOG_W[2], LOG_W[-3], 400)


def knee_two_segment(D):
    """Breakpoint of the best continuous two-piece linear fit in log-log."""
    y = np.log(D)
    best, best_sse = np.nan, np.inf
    for b in BREAKPOINTS:
        X = np.column_stack([np.ones_like(LOG_W), LOG_W,
                             np.maximum(LOG_W - b, 0.0)])
        coef, *_ = np.linalg.lstsq(X, y, rcond=None)
        sse = np.sum((X @ coef - y) ** 2)
        if sse < best_sse:
            best, best_sse = b, sse
    return np.exp(best)


def knee_marginal(D):
    """Smallest w where doubling w improves D by less than the threshold."""
    logD = np.log(D)
    usable = LOG_W + np.log(2) <= LOG_W[-1]
    gain = 1 - np.exp(np.interp(LOG_W[usable] + np.log(2), LOG_W, logD)
                      - logD[usable])
    below = np.nonzero(gain < MARGINAL_THRESHOLD)[0]
    if len(below) == 0:
        return np.nan
    i = below[0]
    if i == 0:
        return FREQUENCIES[0]
    # linear interpolation of the crossing in log w
    t = (gain[i - 1] - MARGINAL_THRESHOLD) / (gain[i - 1] - gain[i])
    return np.exp(LOG_W[i - 1] + t * (LOG_W[i] - LOG_W[i - 1]))


CRITERIA = {"two-segment": knee_two_segment, "marginal": knee_marginal}


def loglog_slope(n_values, knees):
    ok = np.isfinite(knees)
    if ok.sum() < 2:
        return np.nan
    return np.polyfit(np.log(np.asarray(n_values)[ok]), np.log(knees[ok]), 1)[0]


def fit_tail(D, d_inf):
    """Fit D - d_inf = c * w^-beta on w >= TAIL_FROM. Returns (c, beta)."""
    sel = FREQUENCIES >= TAIL_FROM
    excess = D[sel] - d_inf
    sel_pos = excess > 0
    slope, intercept = np.polyfit(LOG_W[sel][sel_pos], np.log(excess[sel_pos]), 1)
    return np.exp(intercept), -slope


# ---------------------------------------------------------------- main

def main():
    rng = np.random.default_rng(11)
    d_inf = floor_distance()

    print("=" * 74)
    print("SATURATION SCALING: does the coverage knee move with n?")
    print("=" * 74)
    print(f"amplitude {AMPLITUDE} (band |y| <= {peak():.3f})  |  "
          f"{POINT_BUDGET} points per n  |  {N_PHASES} phases per w")
    print("prediction under test: w* ~ n  (slope 1.0)")
    print()

    per_trial = per_trial_distances(draw_points(N_VALUES, rng), AMPLITUDE, rng)
    curves_by_n = {n: per_trial[n].mean(axis=0) for n in N_VALUES}

    show = [0, 4, 8, 12, 14, 16, 18, 20, 22, 24]
    print("mean Euclidean distance D(w)")
    print(f"{'w':>8}" + "".join(f"{'n=' + str(n):>10}" for n in N_VALUES))
    for j in show:
        print(f"{FREQUENCIES[j]:>8.1f}" +
              "".join(f"{curves_by_n[n][j]:>10.4f}" for n in N_VALUES))
    print(f"{'inf':>8}" + "".join(f"{d_inf:>10.4f}" for _ in N_VALUES)
          + "   <- band-edge floor, (1 - A*sqrt(2))^2 / 2")
    stacked = np.array([curves_by_n[n] for n in N_VALUES])
    spread = (stacked.max(axis=0) / stacked.min(axis=0) - 1).max()
    print(f"largest relative difference between any two n at any w: "
          f"{100 * spread:.1f}%")

    # knees and slopes, with bootstrap over trials
    print()
    print("knee location w* per n")
    print(f"{'criterion':>12}" + "".join(f"{'n=' + str(n):>9}" for n in N_VALUES)
          + f"{'slope':>9}{'95% CI':>18}")
    knees, slopes, cis = {}, {}, {}
    for name, fn in CRITERIA.items():
        k = np.array([fn(curves_by_n[n]) for n in N_VALUES])
        boot = []
        for _ in range(N_BOOTSTRAP):
            kb = []
            for n in N_VALUES:
                t = per_trial[n]
                kb.append(fn(t[rng.integers(0, len(t), len(t))].mean(axis=0)))
            boot.append(loglog_slope(N_VALUES, np.array(kb)))
        lo, hi = np.nanpercentile(boot, [2.5, 97.5])
        knees[name], slopes[name] = k, loglog_slope(N_VALUES, k)
        cis[name] = (lo, hi)
        print(f"{name:>12}" + "".join(f"{v:>9.1f}" for v in k)
              + f"{slopes[name]:>9.3f}{f'[{lo:.3f}, {hi:.3f}]':>18}")
    print("prediction: slope 1.000")

    # mechanism: band-edge floor plus c/w
    pooled = np.mean([curves_by_n[n] for n in N_VALUES], axis=0)
    c, beta = fit_tail(pooled, d_inf)
    r = MARGINAL_THRESHOLD
    predicted_marginal = c * (1 - 2 * r) / (2 * r * d_inf)
    print()
    print("=" * 74)
    print("MECHANISM: band-edge floor, not point spacing")
    print("=" * 74)
    print(f"fit D - D_inf = c * w^-beta for w >= {TAIL_FROM}:  "
          f"c = {c:.3f}, beta = {beta:.3f}   (band-edge model: beta = 1)")
    print(f"if D = D_inf + c/w, the marginal knee is c(1-2r)/(2r D_inf) = "
          f"{predicted_marginal:.1f}, for every n")

    # control: widen the band to cover the data, floor goes to zero
    ctrl_pts = draw_points([CONTROL_N], rng)
    ctrl = per_trial_distances(ctrl_pts, CONTROL_AMPLITUDE, rng)[CONTROL_N].mean(axis=0)
    c_ctrl, beta_ctrl = fit_tail(ctrl, floor_distance(CONTROL_AMPLITUDE))
    print()
    print(f"control: amplitude {CONTROL_AMPLITUDE:.3f} (band |y| <= "
          f"{peak(CONTROL_AMPLITUDE):.3f}, covers the data), n = {CONTROL_N}")
    print(f"  D(w=1) = {ctrl[0]:.4f}   D(w=100) = {ctrl[16]:.5f}   "
          f"D(w=1000) = {ctrl[-1]:.5f}")
    print(f"  tail fit: D = {c_ctrl:.3f} * w^-{beta_ctrl:.3f}  (no floor)")
    k_marg = knee_marginal(ctrl)
    print(f"  knees: two-segment {knee_two_segment(ctrl):.1f}, marginal "
          + ("none (every doubling still gains >= 10%)" if np.isnan(k_marg)
             else f"{k_marg:.1f}"))

    print()
    holds = all(lo <= 1.0 <= hi for lo, hi in cis.values())
    print(f"slope 1.0 inside every 95% CI: {holds}")
    if not holds:
        print("d-dimensional extension not run: it is conditional on the 1-D")
        print("prediction holding (TASKS.md, task 9).")

    if HAVE_PLT:
        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(14, 6))
        colors = plt.cm.viridis(np.linspace(0, 0.9, len(N_VALUES)))
        for n, col in zip(N_VALUES, colors):
            ax1.loglog(FREQUENCIES, curves_by_n[n], "o-", color=col, ms=4,
                       lw=1.5, label=f"n = {n}")
        ax1.loglog(FREQUENCIES, ctrl, "s--", color="tab:red", ms=4, lw=1.5,
                   label=f"control: band covers data (n = {CONTROL_N})")
        ax1.axhline(d_inf, color="gray", ls=":", lw=1.5,
                    label=f"band-edge floor {d_inf:.4f}")
        for name, marker in [("two-segment", "v"), ("marginal", "^")]:
            w = np.nanmedian(knees[name])
            ax1.axvline(w, color="k", ls="-." if marker == "v" else ":",
                        lw=1, alpha=0.6, label=f"{name} knee (median) {w:.0f}")
        ax1.set_xlabel("frequency w")
        ax1.set_ylabel("mean Euclidean distance D")
        ax1.set_title("Mean distance vs frequency, by n")
        ax1.legend(fontsize=8)
        ax1.grid(alpha=0.3, which="both")

        n_arr = np.array(N_VALUES, dtype=float)
        for name, marker in [("two-segment", "v"), ("marginal", "^")]:
            ax2.loglog(n_arr, knees[name], marker, ms=9,
                       label=f"{name}: slope {slopes[name]:.2f}")
        anchor = np.nanmedian(knees["two-segment"])
        ax2.loglog(n_arr, anchor * n_arr / n_arr[2], "k--", lw=1,
                   label="prediction w* ~ n (slope 1)")
        ax2.set_xlabel("number of points n")
        ax2.set_ylabel("knee frequency w*")
        ax2.set_title("Knee frequency vs n")
        ax2.legend(fontsize=9)
        ax2.grid(alpha=0.3, which="both")

        plt.tight_layout()
        plt.savefig("../graphs/saturation_scaling.png", dpi=200,
                    bbox_inches="tight")
        plt.close()
        print("\nSaved ../graphs/saturation_scaling.png")


if __name__ == "__main__":
    main()
