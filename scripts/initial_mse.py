"""
initial_mse.py

Does a wider random ReLU network start with a lower loss? No, and the answer
is an identity, not a measurement.

For a network whose last layer has zero-mean weights, E[f(x)] = 0, so

    E[MSE at initialisation] = E[y^2] + E[f(x)^2].

Under He initialisation every layer preserves the second moment exactly at
every width: E[f(x)^2] = 2 * |x|^2 / d_in. So the expected initial MSE does
not depend on width. With unscaled N(0, 1) weights each hidden layer multiplies
the second moment by width / 2, and the initial MSE grows with width.

This is the network version of the marginal lemma in lean/SquigglyLine/Marginal.lean:
the expected loss reads only the distribution of f(x) at each single x.

Setup: 10 inputs, 200 points, x and y uniform on [-1, 1], two hidden layers,
no biases, 200 random networks per width.

Run:  python initial_mse.py      (numpy, ~1 minute)
"""

import numpy as np

D_IN = 10
N_POINTS = 200
N_HIDDEN = 2
N_NETS = 200
WIDTHS = [4, 16, 64, 256, 1024]


def initial_mse(width, he, x, y, rng):
    """Mean and standard error of the MSE of N_NETS untrained networks."""
    losses = np.empty(N_NETS)
    for k in range(N_NETS):
        h, fan_in = x, D_IN
        for _ in range(N_HIDDEN):
            std = np.sqrt(2.0 / fan_in) if he else 1.0
            h = np.maximum(h @ rng.normal(scale=std, size=(fan_in, width)), 0.0)
            fan_in = width
        std = np.sqrt(2.0 / fan_in) if he else 1.0
        out = h @ rng.normal(scale=std, size=fan_in)
        losses[k] = np.mean((out - y) ** 2)
    return losses.mean(), losses.std() / np.sqrt(N_NETS)


def main():
    rng = np.random.default_rng(3)
    x = rng.uniform(-1, 1, size=(N_POINTS, D_IN))
    y = rng.uniform(-1, 1, size=N_POINTS)

    second_moment = np.mean((x ** 2).sum(axis=1)) / D_IN      # mean of |x|^2 / d_in
    he_theory = np.mean(y ** 2) + 2 * second_moment

    print(f"{D_IN} inputs, {N_POINTS} points, {N_HIDDEN} hidden layers, "
          f"{N_NETS} networks per width")
    print()
    print(f"{'width':>6} {'He init':>18} {'He theory':>10} {'unscaled':>12} {'unscaled theory':>16}")
    print("-" * 66)
    for width in WIDTHS:
        he, he_se = initial_mse(width, True, x, y, rng)
        raw, _ = initial_mse(width, False, x, y, rng)
        raw_theory = np.mean(y ** 2) + D_IN * second_moment * (width / 2) ** N_HIDDEN
        print(f"{width:>6} {he:>10.3f} +- {he_se:.3f} {he_theory:>10.3f} "
              f"{raw:>12.3g} {raw_theory:>16.3g}")


if __name__ == "__main__":
    main()
