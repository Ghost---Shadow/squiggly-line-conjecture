"""
fourier_params.py

What does adding parameters change? A family where the parameter count is the
only dial.

Model:  f(x) = a_0 + sum_{k=1..m} a_k cos(k pi x) + b_k sin(k pi x)
        P = 2m + 1 parameters, drawn N(0, V / (m + 1)).
        The scaling keeps the output variance at V for every m, so the
        distribution of f(x) at a single x does not depend on m.

Data:   n points, x uniform on [-1, 1]. Two targets: random labels, and a
        smooth function of x.

Four measurements per m, all before or during plain gradient descent:

    initial MSE     vertical loss of the random function. The marginal lemma
                    says this cannot depend on m.
    nearest dist    Euclidean distance from a data point to the random curve.
    travel          distance in parameter space from the random start to the
                    nearest parameter vector that fits all n points:
                    sqrt(r' K^-1 r), with r the initial residual and
                    K = Phi Phi' the kernel of the features. Exists once P >= n.
    steps           gradient-descent steps to reach MSE <= TOL, with the
                    largest stable step size (computed exactly in the
                    eigenbasis of K).

Run:  python fourier_params.py      (numpy + scipy, ~1 minute)
"""

import numpy as np

from curves import euclid_distance

N_POINTS = 20
V = 1.0 / 3.0                  # output variance, equal to the variance of Uniform(-1, 1)
M_VALUES = [1, 2, 4, 8, 9, 10, 12, 16, 32, 64, 128, 256]
N_DATASETS = 20
N_INITS = 20
NEAREST_MAX_M = 64             # the curve is sampled on a grid; keep it affordable
TOL = 1e-3
MAX_STEPS = 10 ** 12


def features(x, m):
    k = np.arange(1, m + 1) * np.pi
    return np.hstack([np.ones((len(x), 1)), np.cos(np.outer(x, k)), np.sin(np.outer(x, k))])


def steps_to_fit(eigvals, coeffs2, n):
    """Smallest t with (1/n) * sum c_i^2 (1 - lam_i / lam_max)^(2t) <= TOL, or inf."""
    rate = np.clip(1.0 - eigvals / eigvals.max(), 0.0, 1.0)
    loss = lambda t: np.sum(coeffs2 * rate ** (2.0 * t)) / n
    if loss(MAX_STEPS) > TOL:
        return np.inf
    lo, hi = 0, 1
    while loss(hi) > TOL:
        lo, hi = hi, hi * 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        lo, hi = (lo, mid) if loss(mid) <= TOL else (mid, hi)
    return hi


def measure(m, x, y, rng):
    n = len(x)
    phi = features(x, m)
    kernel = phi @ phi.T
    eigvals, eigvecs = np.linalg.eigh(kernel)
    eigvals = np.maximum(eigvals, 0.0)
    fits = phi.shape[1] >= n
    out = {"mse": [], "nearest": [], "travel": [], "rel_travel": [], "steps": []}
    grid = np.linspace(-1, 1, max(4000, 800 * m)) if m <= NEAREST_MAX_M else None
    phi_grid = features(grid, m) if grid is not None else None
    for _ in range(N_INITS):
        theta = rng.normal(scale=np.sqrt(V / (m + 1)), size=phi.shape[1])
        resid = y - phi @ theta
        out["mse"].append(np.mean(resid ** 2))
        if phi_grid is not None:
            out["nearest"].append(euclid_distance(grid, phi_grid @ theta, x, y).mean())
        if fits:
            keep = eigvals > 1e-12 * eigvals.max()
            travel = np.sqrt(np.sum((eigvecs.T @ resid)[keep] ** 2 / eigvals[keep]))
            out["travel"].append(travel)
            out["rel_travel"].append(travel / np.linalg.norm(theta))
        out["steps"].append(steps_to_fit(eigvals, (eigvecs.T @ resid) ** 2, n))
    return out


def sweep(target, rng):
    rows = []
    for m in M_VALUES:
        acc = {}
        for _ in range(N_DATASETS):
            x = rng.uniform(-1, 1, N_POINTS)
            y = rng.uniform(-1, 1, N_POINTS) if target == "random" else 0.8 * np.sin(1.5 * np.pi * x)
            for key, vals in measure(m, x, y, rng).items():
                acc.setdefault(key, []).extend(vals)
        rows.append((m, 2 * m + 1,
                     np.mean(acc["mse"]),
                     np.mean(acc["nearest"]) if acc["nearest"] else np.nan,
                     np.median(acc["travel"]) if acc["travel"] else np.nan,
                     np.median(acc["rel_travel"]) if acc["rel_travel"] else np.nan,
                     np.median(acc["steps"])))
    return rows


def main():
    rng = np.random.default_rng(5)
    print(f"{N_POINTS} points, output variance {V:.3f} at every m, "
          f"{N_DATASETS} datasets x {N_INITS} random starts per m")
    print(f"a fit of all points exists once P >= {N_POINTS}")
    for target in ["random", "smooth"]:
        print()
        print(f"target: {target} labels" if target == "random" else "target: 0.8 sin(1.5 pi x)")
        print(f"{'m':>4} {'params':>7} {'init MSE':>9} {'nearest':>9} {'travel':>9} "
              f"{'travel/|start|':>15} {'GD steps':>10}")
        print("-" * 70)
        for m, p, mse, nearest, travel, rel, steps in sweep(target, rng):
            fmt = lambda v, f: "-" if np.isnan(v) else ("never" if np.isinf(v) else format(v, f))
            print(f"{m:>4} {p:>7} {mse:>9.3f} {fmt(nearest, '9.4f'):>9} {fmt(travel, '9.3f'):>9} "
                  f"{fmt(rel, '15.3f'):>15} {fmt(steps, '10.0f'):>10}")


if __name__ == "__main__":
    main()
