"""
double_descent.py

Is the double-descent peak the travel peak?

The Fourier model of fourier_params.py, now fitted and tested. For each number
of parameters P the model is fitted to n noisy points and scored on fresh
points:

    P <  n : least squares (no exact fit exists);
    P >= n : the fit nearest to the start, which is where gradient descent
             from that start ends up. The start is zero.

Two versions of the features:

    flat     : every term has the same scale;
    decaying : term k is scaled by 1/k, so high frequencies cost more to use.

Measured for each P, over many data sets:

    test MSE   error on fresh points against the noise-free target;
    travel     distance in parameter space from the start to the fit;
    weakest    smallest eigenvalue of the kernel K = A A' (for P >= n).
               Kernel.lean proves travel <= |labels| / sqrt(weakest).

Run:  python double_descent.py      (numpy + matplotlib, ~1 minute)
"""

from pathlib import Path

import numpy as np

N_TRAIN = 20
N_TEST = 2000
NOISE = 0.2
N_DATASETS = 300
P_VALUES = [3, 5, 9, 13, 17, 19, 21, 23, 25, 33, 65, 129, 257, 513]
GRAPHS = Path(__file__).resolve().parent.parent / "graphs"


def target(x):
    return 0.8 * np.sin(1.5 * np.pi * x)


def features(x, m, decaying):
    k = np.arange(1, m + 1)
    scale = 1.0 / k if decaying else np.ones(m)
    return np.hstack([np.ones((len(x), 1)),
                      np.cos(np.outer(x, k * np.pi)) * scale,
                      np.sin(np.outer(x, k * np.pi)) * scale])


def sweep(decaying, rng):
    """One row per P: (P, median test MSE, median travel, median weakest eigenvalue)."""
    rows = []
    x_test = np.linspace(-1, 1, N_TEST)
    for p in P_VALUES:
        m = (p - 1) // 2
        test, travel, weakest = [], [], []
        for _ in range(N_DATASETS):
            x = rng.uniform(-1, 1, N_TRAIN)
            y = target(x) + rng.normal(scale=NOISE, size=N_TRAIN)
            a = features(x, m, decaying)
            theta = np.linalg.lstsq(a, y, rcond=None)[0]      # least squares; nearest fit if P >= n
            test.append(np.mean((features(x_test, m, decaying) @ theta - target(x_test)) ** 2))
            travel.append(np.linalg.norm(theta))
            if p >= N_TRAIN:
                weakest.append(np.linalg.eigvalsh(a @ a.T)[0])
        rows.append((p, np.median(test), np.median(travel),
                     np.median(weakest) if weakest else np.nan))
    return rows


def plot(results):
    import matplotlib.pyplot as plt

    import readme_figures as style          # shared colours and rcParams

    fig, axes = plt.subplots(2, 1, figsize=(9.5, 7.6), sharex=True)
    series = [("flat", "every term at the same scale", style.NEAREST),
              ("decaying", "term k scaled by 1/k", style.CONTROL)]
    for ax, column, label in [(axes[0], 1, "test error (MSE on fresh points)"),
                              (axes[1], 2, "travel (distance from the start to the fit)")]:
        for key, name, colour in series:
            rows = np.array(results[key])
            ax.plot(rows[:, 0], rows[:, column], color=colour, label=name, **style.MARKER)
        ax.axvline(N_TRAIN, color=style.AXIS, lw=1.0, zorder=1)
        ax.set_yscale("log")
        ax.set_ylabel(label)
        ax.minorticks_off()
    axes[0].set_title("The test-error peak and the travel peak are the same peak")
    axes[0].annotate("as many parameters as points", (N_TRAIN, axes[0].get_ylim()[1]),
                     xytext=(16, -30), textcoords="offset points", color=style.MUTED, fontsize=9.5)
    axes[0].legend(loc="upper right")
    axes[1].set_xscale("log", base=2)
    axes[1].set_xticks([4, 8, 16, 32, 64, 128, 256, 512])
    axes[1].set_xticklabels(["4", "8", "16", "32", "64", "128", "256", "512"])
    axes[1].set_xlabel("number of parameters")
    fig.tight_layout()
    path = GRAPHS / "double_descent.png"
    fig.savefig(path, dpi=200, bbox_inches="tight", pad_inches=0.25)
    plt.close(fig)
    print(f"saved {path.relative_to(GRAPHS.parent)}")


def main():
    rng = np.random.default_rng(9)
    print(f"{N_TRAIN} training points, noise {NOISE}, target 0.8 sin(1.5 pi x), "
          f"{N_DATASETS} data sets per P; medians")
    print(f"error of predicting zero everywhere: {np.mean(target(np.linspace(-1, 1, N_TEST)) ** 2):.3f}")
    results = {}
    for key, decaying in [("flat", False), ("decaying", True)]:
        results[key] = sweep(decaying, rng)
        print()
        print(f"features: {key}")
        print(f"{'params':>7} {'test MSE':>12} {'travel':>12} {'weakest eig':>12} "
              f"{'|y|/sqrt(eig)':>14}")
        print("-" * 62)
        for p, test, travel, weakest in results[key]:
            bound = "-" if np.isnan(weakest) else f"{np.sqrt(N_TRAIN * 0.36) / np.sqrt(weakest):14.3g}"
            eig = "-" if np.isnan(weakest) else f"{weakest:12.3g}"
            print(f"{p:>7} {test:>12.4g} {travel:>12.4g} {eig:>12} {bound:>14}")
    try:
        plot(results)
    except ImportError:
        pass


if __name__ == "__main__":
    main()
