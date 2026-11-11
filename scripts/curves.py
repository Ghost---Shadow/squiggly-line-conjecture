"""
curves.py

Shared geometry for the sine-curve coverage experiments
(frequency_isolation.py, saturation_scaling.py).

Curves are f(x) = A * sqrt(2) * sin(w * pi * x + phi) on x in [-1, 1].
Data points are uniform on [-1, 1]^2.

Numerical note
--------------
The first version of frequency_isolation.py sampled every curve on a fixed
4000-point grid. At frequency w the curve's steepest slope is A*sqrt(2)*w*pi,
so consecutive grid samples were up to ~0.08 apart vertically at w = 64 --
larger than the distances being measured. Euclidean distance was therefore
overestimated at high frequency, producing a spurious plateau at ~0.028 from
w ~ 32 onward.

Here the grid is sized per frequency so that consecutive samples are at most
RESOLUTION apart along the curve, and the distance to the polyline is exact
(see euclid_distance).

Second correction (11 Nov 2026). Until then the nearest-sample distance was
refined only on the two segments adjacent to the nearest sample. Once the
spacing between neighbouring strokes of the sine (1/w) drops below RESOLUTION,
the nearest sample can sit on the wrong stroke, and the refinement then
returns the distance to that stroke. With the band covering the data this
overestimated the mean distance by 11% at w = 1000 (0.000324 against 0.000292)
and by 0.05% at w = 250. With the default amplitude the band-edge floor
dominates and the error was 0.2% at w = 1000.
"""

import numpy as np
from scipy.spatial import cKDTree

AMPLITUDE = 0.577          # std of Uniform(-1, 1), matching the data
RESOLUTION = 0.002         # max spacing between consecutive curve samples
MIN_GRID = 4000


def peak(amplitude=AMPLITUDE):
    """Half-height of the band the sine sweeps out."""
    return amplitude * np.sqrt(2)


def floor_distance(amplitude=AMPLITUDE):
    """
    Limit of the expected Euclidean distance as frequency -> infinity.

    The curve fills the band |y| <= peak densely, so points inside it are
    reached at distance -> 0. Points outside it can never get closer than
    |y| - peak. For y ~ Uniform(-1, 1): E[max(0, |y| - p)] = (1 - p)^2 / 2.
    """
    p = peak(amplitude)
    return max(0.0, 1.0 - p) ** 2 / 2


def sine_grid(freq, amplitude=AMPLITUDE, h=RESOLUTION):
    """x-grid fine enough that the curve moves at most h between samples."""
    slope = peak(amplitude) * freq * np.pi
    n = max(MIN_GRID, int(np.ceil(2 * np.hypot(1.0, slope) / h)) + 1)
    return np.linspace(-1, 1, n)


def sine_curve(freq, phi, x, amplitude=AMPLITUDE):
    return peak(amplitude) * np.sin(freq * np.pi * x + phi)


def phase_pool(n, rng):
    """Stratified random phases: one uniform draw in each of n equal bins."""
    return 2 * np.pi * (np.arange(n) + rng.uniform(size=n)) / n


def arclen(x, y):
    """Arc length of the polyline (x, y)."""
    return np.hypot(np.diff(x), np.diff(y)).sum()


def _segment_distance(ax, ay, bx, by, px, py):
    dx, dy = bx - ax, by - ay
    t = ((px - ax) * dx + (py - ay) * dy) / np.maximum(dx * dx + dy * dy, 1e-300)
    t = np.clip(t, 0.0, 1.0)
    return np.hypot(px - (ax + t * dx), py - (ay + t * dy))


def euclid_distance(x, y, px, py):
    """
    Per-point minimum Euclidean distance from (px, py) to the polyline (x, y).
    Exact for the polyline. Returns an array shaped like px.

    Let d0 be the distance to the nearest sample and `step` the longest
    segment. The nearest point of the polyline is at distance d <= d0 and
    lies on a segment that has an endpoint within step/2 of it, so that
    endpoint is within d0 + step/2 of the query point. Projecting onto both
    segments adjacent to every sample inside that ball therefore finds it.
    """
    shape = np.shape(px)
    px, py = np.ravel(px), np.ravel(py)
    pts = np.column_stack([px, py])
    tree = cKDTree(np.column_stack([x, y]))
    d0, _ = tree.query(pts)
    step = np.hypot(np.diff(x), np.diff(y)).max()
    balls = tree.query_ball_point(pts, d0 + step / 2)
    counts = np.fromiter((len(b) for b in balls), dtype=np.intp, count=len(balls))
    i = np.concatenate(balls).astype(np.intp)
    qx, qy = np.repeat(px, counts), np.repeat(py, counts)
    lo = np.maximum(i - 1, 0)
    hi = np.minimum(i + 1, len(x) - 1)
    d = np.minimum(_segment_distance(x[lo], y[lo], x[i], y[i], qx, qy),
                   _segment_distance(x[i], y[i], x[hi], y[hi], qx, qy))
    starts = np.concatenate([[0], np.cumsum(counts)[:-1]])
    return np.minimum.reduceat(d, starts).reshape(shape)


def vertical_distance(freq, phi, px, py, amplitude=AMPLITUDE):
    """Per-point |y - f(x)| -- what a regression loss sees."""
    return np.abs(py - sine_curve(freq, phi, px, amplitude))


def matched_length_slope(target_length):
    """Slope m of a line y = m*x + b over [-1, 1] with the given arc length."""
    return np.sqrt((target_length / 2.0) ** 2 - 1.0)


def line_distance(m, b, px, py):
    """Exact per-point distance to the segment y = m*x + b, x in [-1, 1]."""
    return _segment_distance(-1.0, b - m, 1.0, b + m, px, py)
