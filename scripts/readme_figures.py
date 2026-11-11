"""
readme_figures.py

Draws the four figures of README.md into graphs/. Every number plotted is
computed here from the same functions the experiments use; nothing is typed in.

    readme_two_distances.png   the two distances, on one smooth and one squiggly curve
    readme_frequency.png       both distances against frequency, with the slope bound
    readme_floor.png           the floor, and the control that has none
    readme_initial_mse.png     initial MSE of random ReLU networks against width

Colour follows the quantity in every figure: blue is the nearest-point
distance, orange is the vertical error, green is the control amplitude.

Run:  python readme_figures.py      (numpy + scipy + matplotlib, ~2 minutes)
"""

from pathlib import Path

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

import frequency_isolation
import initial_mse
from curves import (AMPLITUDE, euclid_distance, floor_distance, peak, phase_pool,
                    sine_curve, sine_grid, vertical_distance)

GRAPHS = Path(__file__).resolve().parent.parent / "graphs"

SURFACE = "#fcfcfb"
TEXT = "#0b0b0b"
TEXT_SECONDARY = "#52514e"
MUTED = "#898781"
GRID = "#e1e0d9"
AXIS = "#c3c2b7"
NEAREST = "#2a78d6"      # blue: nearest-point distance
VERTICAL = "#eb6834"     # orange: vertical error
CONTROL = "#1baf7a"      # green: amplitude that covers the data

CONTROL_AMPLITUDE = 1 / np.sqrt(2)
CONTROL_SLOPE = (2 - 8 / np.pi ** 2) / 4      # D * w -> 0.2974 when the band covers the data

plt.rcParams.update({
    "figure.facecolor": SURFACE, "axes.facecolor": SURFACE, "savefig.facecolor": SURFACE,
    "font.family": "DejaVu Sans", "font.size": 11,
    "text.color": TEXT, "axes.labelcolor": TEXT_SECONDARY, "axes.titlecolor": TEXT,
    "axes.titlesize": 12, "axes.titleweight": "bold", "axes.titlelocation": "left",
    "xtick.color": MUTED, "ytick.color": MUTED, "xtick.labelcolor": TEXT_SECONDARY,
    "ytick.labelcolor": TEXT_SECONDARY,
    "axes.edgecolor": AXIS, "axes.linewidth": 1.0,
    "axes.spines.top": False, "axes.spines.right": False,
    "axes.grid": True, "grid.color": GRID, "grid.linewidth": 1.0, "grid.linestyle": "-",
    "axes.axisbelow": True,
    "lines.linewidth": 2.0, "lines.solid_capstyle": "round", "lines.solid_joinstyle": "round",
    "legend.frameon": False, "legend.fontsize": 10,
})

MARKER = dict(marker="o", markersize=8, markeredgecolor=SURFACE, markeredgewidth=2)


def save(fig, name):
    path = GRAPHS / name
    fig.savefig(path, dpi=200, bbox_inches="tight", pad_inches=0.25)
    plt.close(fig)
    print(f"saved {path.relative_to(GRAPHS.parent)}")


def mean_distances(freq, amplitude, px, py, phases):
    """Mean nearest-point distance and mean vertical error over points and phases."""
    x = sine_grid(freq, amplitude)
    nearest, vertical = [], []
    for phi in phases:
        nearest.append(euclid_distance(x, sine_curve(freq, phi, x, amplitude), px, py).mean())
        vertical.append(vertical_distance(freq, phi, px, py, amplitude).mean())
    return np.mean(nearest), np.mean(vertical)


# ----------------------------------------------------------------- figure 1

def two_distances(rng):
    """One set of points, a smooth curve and a squiggly one, both distances drawn."""
    px, py = rng.uniform(-0.92, 0.92, 16), rng.uniform(-0.75, 0.75, 16)
    phi = 0.6
    fig, axes = plt.subplots(1, 2, figsize=(11, 6.3))
    for ax, freq, name in zip(axes, [1, 8], ["A smooth curve", "A squiggly curve"]):
        x = np.linspace(-1, 1, 40001)
        y = sine_curve(freq, phi, x)
        gap = np.hypot(px[:, None] - x[None, :], py[:, None] - y[None, :])
        hit = gap.argmin(axis=1)
        nearest = gap.min(axis=1).mean()
        vertical = np.abs(py - sine_curve(freq, phi, px)).mean()

        ax.plot(x, y, color=TEXT_SECONDARY, lw=1.6, zorder=2)
        for k in range(len(px)):
            ax.plot([px[k], px[k]], [py[k], sine_curve(freq, phi, px[k])],
                    color=VERTICAL, zorder=3, label="vertical error  |y − f(x)|" if k == 0 else None)
            ax.plot([px[k], x[hit[k]]], [py[k], y[hit[k]]],
                    color=NEAREST, zorder=4, label="distance to the nearest point" if k == 0 else None)
        ax.plot(px, py, ls="none", color=TEXT, zorder=5, **MARKER)

        ax.set_title(name, pad=26)
        ax.text(0, 1.02, f"mean nearest {nearest:.2f}   ·   mean vertical {vertical:.2f}",
                transform=ax.transAxes, va="bottom", color=TEXT_SECONDARY, fontsize=10.5)
        ax.set_xlim(-1.02, 1.02)
        ax.set_ylim(-1.02, 1.02)
        ax.set_aspect("equal")
        ax.set_xticks([-1, 0, 1])
        ax.set_yticks([-1, 0, 1])
        ax.grid(False)
    axes[0].set_ylabel("y")
    for ax in axes:
        ax.set_xlabel("x")
    handles, labels = axes[0].get_legend_handles_labels()
    fig.legend(handles[::-1], labels[::-1], loc="lower center", ncol=2, bbox_to_anchor=(0.5, 0.0))
    fig.subplots_adjust(left=0.07, right=0.98, top=0.80, bottom=0.17, wspace=0.14)
    fig.text(0.07, 0.94, "The same 16 points. Squiggling shortens the blue lines and not the orange ones.",
             ha="left", va="center", fontsize=13, fontweight="bold")
    save(fig, "readme_two_distances.png")


# ----------------------------------------------------------------- figure 2

def frequency():
    """Both distances against frequency, with the lower bound of the slope sandwich."""
    freqs = np.array(frequency_isolation.FREQUENCIES)
    _, _, rows = frequency_isolation.sweep(np.random.default_rng(7))   # same run as the table
    _, nearest, vertical = np.array(rows).T
    slope = peak() * freqs * np.pi
    bound = vertical / np.hypot(1.0, slope)

    fig, ax = plt.subplots(figsize=(9.5, 5.6))
    ax.fill_between(freqs, bound, vertical, color=NEAREST, alpha=0.07, lw=0, zorder=1)
    ax.plot(freqs, bound, color=MUTED, lw=1.2, zorder=2, label="lower bound  vertical / √(1 + K²)")
    ax.axhline(floor_distance(), color=AXIS, lw=1.0, zorder=2)
    ax.plot(freqs, vertical, color=VERTICAL, zorder=4, label="vertical error (what training sees)", **MARKER)
    ax.plot(freqs, nearest, color=NEAREST, zorder=5, label="distance to the nearest point", **MARKER)

    ax.set_xscale("log", base=2)
    ax.set_yscale("log")
    ax.set_xticks(freqs)
    ax.set_xticklabels([f"{w:g}" for w in freqs])
    ax.set_yticks([0.003, 0.01, 0.03, 0.1, 0.3, 1])
    ax.set_yticklabels(["0.003", "0.01", "0.03", "0.1", "0.3", "1"])
    ax.minorticks_off()
    ax.set_ylim(0.003, 1.3)
    ax.set_xlabel("frequency of the curve (amplitude fixed)")
    ax.set_ylabel("mean distance to random points")
    ax.set_title("Squiggliness moves one distance and not the other")

    ax.annotate(f"{vertical[-1]:.2f}, unchanged", (freqs[-1], vertical[-1]), xytext=(-8, 12),
                textcoords="offset points", ha="right", color=TEXT_SECONDARY, fontsize=10)
    ax.annotate(f"{nearest[-1]:.3f}, {nearest[0] / nearest[-1]:.0f}× closer", (freqs[-1], nearest[-1]),
                xytext=(-4, 40), textcoords="offset points", ha="right", color=TEXT_SECONDARY, fontsize=10)
    ax.annotate(f"floor {floor_distance():.4f}: points outside the band stay out of reach",
                (freqs[0], floor_distance()), xytext=(0, 5), textcoords="offset points",
                color=MUTED, fontsize=9.5)
    ax.legend(loc="lower left")
    save(fig, "readme_frequency.png")


# ----------------------------------------------------------------- figure 3

def floor(rng):
    """The floor comes from the amplitude: widen the band and the floor is gone."""
    freqs = np.logspace(0, np.log10(256), 17)
    px, py = rng.uniform(-1, 1, 1500), rng.uniform(-1, 1, 1500)
    default = np.array([mean_distances(w, AMPLITUDE, px, py, phase_pool(6, rng))[0] for w in freqs])
    control = np.array([mean_distances(w, CONTROL_AMPLITUDE, px, py, phase_pool(6, rng))[0]
                        for w in freqs])

    fig, ax = plt.subplots(figsize=(9.5, 5.6))
    ax.plot(freqs, CONTROL_SLOPE / freqs, color=MUTED, lw=1.2, zorder=2,
            label="closed form  0.2974 / frequency")
    ax.axhline(floor_distance(), color=AXIS, lw=1.0, zorder=2)
    ax.plot(freqs, default, color=NEAREST, zorder=4,
            label=f"band |y| ≤ {peak():.2f}: some points out of reach", **MARKER)
    ax.plot(freqs, control, color=CONTROL, zorder=5, label="band |y| ≤ 1: covers the data", **MARKER)

    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xticks([1, 3, 10, 30, 100, 256])
    ax.set_xticklabels(["1", "3", "10", "30", "100", "256"])
    ax.set_yticks([0.001, 0.003, 0.01, 0.03, 0.1, 0.3])
    ax.set_yticklabels(["0.001", "0.003", "0.01", "0.03", "0.1", "0.3"])
    ax.minorticks_off()
    ax.set_xlabel("frequency of the curve")
    ax.set_ylabel("mean distance to the nearest point")
    ax.set_title("The floor is set by the amplitude, not by squiggliness")
    ax.annotate(f"levels off at the floor, {floor_distance():.4f}", (freqs[-1], default[-1]),
                xytext=(-6, 30), textcoords="offset points", ha="right", color=TEXT_SECONDARY, fontsize=10)
    ax.annotate(f"{control[-1]:.4f} and still falling", (freqs[-1], control[-1]), xytext=(-16, -3),
                textcoords="offset points", ha="right", va="center", color=TEXT_SECONDARY, fontsize=10)
    ax.legend(loc="lower left")
    save(fig, "readme_floor.png")


# ----------------------------------------------------------------- figure 4

def initial_loss():
    """Initial MSE of untrained ReLU networks: flat in width, at the predicted value."""
    predicted, rows = initial_mse.sweep()                              # same run as the table
    widths, mean, sem = np.array(rows)[:, :3].T
    widths = widths.astype(int)

    fig, ax = plt.subplots(figsize=(9.5, 4.6))
    ax.axhline(predicted, color=MUTED, lw=1.2, zorder=2, label=f"predicted  E[y²] + E[f(x)²] = {predicted:.2f}")
    ax.errorbar(widths, mean, yerr=2 * sem, color=VERTICAL, ecolor=VERTICAL, elinewidth=1.4,
                capsize=0, zorder=4, label="measured, 200 networks per width (bars: ±2 s.e.)", **MARKER)
    ax.set_xscale("log", base=2)
    ax.set_xticks(widths)
    ax.set_xticklabels([str(w) for w in widths])
    ax.minorticks_off()
    ax.set_ylim(0, 1.6)
    ax.set_yticks([0, 0.5, 1.0, 1.5])
    ax.set_xlabel("width of the network (He initialisation)")
    ax.grid(axis="x", visible=False)
    ax.set_ylabel("MSE before training")
    ax.set_title("A wider random network does not start closer")
    ax.legend(loc="lower left")
    save(fig, "readme_initial_mse.png")


def main():
    rng = np.random.default_rng(2026)
    two_distances(rng)
    frequency()
    floor(rng)
    initial_loss()


if __name__ == "__main__":
    main()
