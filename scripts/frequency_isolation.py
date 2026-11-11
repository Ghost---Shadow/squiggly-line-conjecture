"""
frequency_isolation.py

The decisive experiment for the Squiggly Line Conjecture.

Every earlier experiment in this repository varied "squiggliness" by varying
polynomial degree or network width. That confounds three things at once:
oscillation frequency, output amplitude, and arc length. This script varies
one thing only.

Design
------
Curves are sines:  f(x) = A * sqrt(2) * sin(w * pi * x + phi)

    - A is FIXED for every curve, chosen to equal the standard deviation of
      the data's y values. So the marginal distribution of f(x) at any given
      x is *identical* for every frequency.
    - phi is uniform random, so no curve is privileged by alignment.
    - w (frequency) is the only thing that changes. This is squiggliness,
      cleanly isolated.

Two distances are measured against the same random point cloud:

    euclid : mean over points of the minimum 2-D Euclidean distance from the
             point to the curve. This is the metric used throughout the
             original repo (utils.measure_true_geometric_distance).

    vert   : mean absolute vertical residual |y_i - f(x_i)|. This is what a
             regression loss actually charges you.

Null model
----------
The fishing-line story says the mechanism is arc length: a longer curve has
more chances to pass near a point. To test that directly we compare each
wiggly curve against a STRAIGHT LINE stretched to exactly the same arc
length (y = m*x + b with L = 2*sqrt(1+m^2)). If arc length alone were the
mechanism, the two should score alike.

Caveat (11 Nov 2026): at the lengths tested the line is nearly vertical and
about 99% of it lies outside the data box. So the comparison shows that length
outside the data region buys nothing. It does not show that length is
irrelevant: length inside the region is necessary (docs/RESOLUTION.md, sec. 2).

Result
------
    1. Under `euclid`, squiggliness helps enormously (~30x).
    2. Under `vert`, squiggliness does nothing at all. Flat to <1% across a
       100x change in arc length.
    3. The arc-length-matched straight line does NOT reproduce the effect,
       so arc length alone is not the mechanism. The length has to be spread
       across the data region.

Conclusion: the geometric claim holds and the learning claim does not. The
squiggly curve really is closer to the data -- but only in a direction that
the loss does not measure at the start. A shift of the input can use the
nearness (docs/phase-matching.md); the initial loss cannot see it.

Run:  python frequency_isolation.py
"""

import numpy as np

from curves import (AMPLITUDE, RESOLUTION, arclen, euclid_distance,
                    floor_distance, line_distance, matched_length_slope,
                    phase_pool, sine_curve, sine_grid, vertical_distance)

try:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    HAVE_PLT = True
except ImportError:
    HAVE_PLT = False

TRIALS = 3000
N_POINTS = 30
N_PHASES = 100             # stratified phase pool; trial t uses curve t % N_PHASES
FREQUENCIES = [0.25, 0.5, 1, 2, 4, 8, 16, 32, 64]
NULL_FREQUENCIES = [4, 16, 64]


def measure(freq, phases, px, py):
    """Mean arc length, Euclidean distance and vertical residual at freq."""
    x = sine_grid(freq)
    lengths, euclid, vert = [], np.empty(px.shape), np.empty(px.shape)
    for k, phi in enumerate(phases):
        rows = slice(k, None, len(phases))
        y = sine_curve(freq, phi, x)
        lengths.append(arclen(x, y))
        euclid[rows] = euclid_distance(x, y, px[rows], py[rows])
        vert[rows] = vertical_distance(freq, phi, px[rows], py[rows])
    return np.mean(lengths), euclid.mean(), vert.mean()


def sweep(rng):
    """Draw the points and measure every frequency. Returns (px, py, rows)."""
    px = rng.uniform(-1, 1, size=(TRIALS, N_POINTS))
    py = rng.uniform(-1, 1, size=(TRIALS, N_POINTS))
    rows = [measure(w, phase_pool(N_PHASES, rng), px, py) for w in FREQUENCIES]
    return px, py, rows


def main():
    rng = np.random.default_rng(7)
    px, py, rows = sweep(rng)

    print("=" * 74)
    print("FREQUENCY ISOLATION: squiggliness with amplitude held exactly fixed")
    print("=" * 74)
    print(f"amplitude fixed at {AMPLITUDE}  |  {TRIALS} trials  |  "
          f"{N_POINTS} random points each  |  curve resolution {RESOLUTION}")
    print()
    print(f"{'freq':>6} {'arc length':>12} {'euclid dist':>14} {'vert |resid|':>14}")
    print("-" * 50)

    lengths, euclids, verts = [], [], []
    for w, (L, e, v) in zip(FREQUENCIES, rows):
        lengths.append(L)
        euclids.append(e)
        verts.append(v)
        print(f"{w:>6} {L:>12.2f} {e:>14.4f} {v:>14.4f}")

    print()
    print(f"euclid: {euclids[0]:.4f} -> {euclids[-1]:.4f}   "
          f"({euclids[0] / euclids[-1]:.1f}x improvement)")
    print(f"vert:   {verts[0]:.4f} -> {verts[-1]:.4f}   "
          f"({100 * (verts[0] - verts[-1]) / verts[0]:+.1f}% change)")
    print(f"euclid limit as freq -> inf: {floor_distance():.4f}  "
          f"(points outside the band |y| <= A*sqrt(2) are unreachable)")

    print()
    print("=" * 74)
    print("NULL MODEL: straight line stretched to identical arc length")
    print("=" * 74)
    print("If arc length alone were the mechanism these columns would match.")
    print()
    print(f"{'freq':>6} {'arc length':>12} {'wiggly':>10} {'straight':>10}")
    print("-" * 42)
    b = rng.uniform(-1, 1, size=(TRIALS, 1))
    for w in NULL_FREQUENCIES:
        i = FREQUENCIES.index(w)
        m = matched_length_slope(lengths[i])
        straight = line_distance(m, b, px, py).mean()
        print(f"{w:>6} {lengths[i]:>12.2f} {euclids[i]:>10.4f} {straight:>10.4f}")

    print()
    print("Length outside the data region buys nothing: the straight line leaves the box.")

    if HAVE_PLT:
        plt.figure(figsize=(10, 6))
        plt.semilogx(FREQUENCIES, euclids, "o-", lw=2, ms=8,
                     label="Euclidean min-distance")
        plt.semilogx(FREQUENCIES, verts, "s-", lw=2, ms=8,
                     label="Vertical residual (what loss sees)")
        plt.axhline(floor_distance(), color="gray", ls=":", lw=1.5,
                    label="Euclidean limit, freq -> inf")
        plt.xlabel("Frequency (squiggliness), amplitude held fixed")
        plt.ylabel("Mean distance to random points")
        plt.title("Squiggliness helps geometrically, not vertically")
        plt.ylim(0, 0.75)
        plt.legend()
        plt.grid(alpha=0.3)
        plt.tight_layout()
        plt.savefig("../graphs/frequency_isolation.png", dpi=300,
                    bbox_inches="tight")
        plt.close()
        print("\nSaved ../graphs/frequency_isolation.png")


if __name__ == "__main__":
    main()
