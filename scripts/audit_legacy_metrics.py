"""
audit_legacy_metrics.py

Shows what the original measurement code in this repository actually computes.
Run this before trusting any number in the older scripts or in main.tex.

Three defects, all reproduced below.

1. utils.measure_coverage / more_effects.measure_scaling_vs_dimension
   ------------------------------------------------------------------
   The line labelled "simplified" reads:

       dist = np.abs(yi - np.sum(pattern))

   `pattern` is the boolean activation vector, so `np.sum(pattern)` is the
   NUMBER OF ACTIVE NEURONS -- roughly width/2. This is not a distance to
   anything. It grows linearly with width, so the repo's own core metric
   reports the OPPOSITE of the conjecture while being captioned as evidence
   for it.

2. relu_chain.analyze_squiggly_line_effect, input_dim > 1 branch
   -------------------------------------------------------------
   The metric is ||net(x) - x||: the distance from the network's output to
   its own input. With Xavier init on a 2 -> w -> w -> 2 ReLU stack, the
   first layer has fan_in=2, fan_out=w, so weight variance is 2/(2+w) and
   the signal is attenuated as width grows. The network output decays toward
   zero, so ||net(x) - x|| decays toward the constant ||x||.

   The much-quoted power law L ~ w^(-alpha), alpha ~ 0.42, is this decay.
   It is the measurement of a network progressively outputting nothing. A
   network hard-wired to return 0.0 scores the asymptote exactly.

3. relu_chain.analyze_squiggly_line_effect, input_dim == 1 branch
   --------------------------------------------------------------
       dists = torch.sqrt((x_curve - point[0])**2 + (y_curve - point[0])**2)
                                                                  ^^^^^^^^
   `point[0]` is used for both coordinates, so every "random data point" is
   silently placed on the diagonal y = x. The comment even flags it
   ("Using point[0] as y-value too for simplicity"). The point cloud this
   branch measures against is not the point cloud it generated.

Run:  python audit_legacy_metrics.py
"""

import numpy as np

from utils import measure_coverage


def audit_activation_count_metric():
    print("=" * 70)
    print("1. utils.measure_coverage -- the 'simplified distance measure'")
    print("=" * 70)
    print("Claimed: distance to the data. Actual: |y - (#active neurons)|.")
    print()
    np.random.seed(0)
    print(f"{'width':>8} {'repo avg_distance':>20} {'width/2':>10}")
    print("-" * 42)
    for n in [10, 20, 40, 80, 160]:
        dist, _ = measure_coverage(n, d=3, m=300, trials=20)
        print(f"{n:>8} {dist:>20.3f} {n / 2:>10.1f}")
    print()
    print("It tracks width/2. It increases with width. The conjecture")
    print("predicts a decrease. This metric was never evidence either way.")


def audit_output_decay_metric():
    print()
    print("=" * 70)
    print("2. relu_chain -- the ||net(x) - x|| metric behind alpha ~ 0.42")
    print("=" * 70)
    rng = np.random.default_rng(0)

    def xavier(fan_in, fan_out):
        lim = np.sqrt(6.0 / (fan_in + fan_out))
        return rng.uniform(-lim, lim, size=(fan_in, fan_out))

    pts = rng.normal(size=(50, 2))
    print(f"{'width':>8} {'||net(x) - x||':>18}")
    print("-" * 28)
    for w in [2, 4, 8, 16, 32, 64, 128]:
        vals = []
        for _ in range(200):
            W1, W2, W3 = xavier(2, w), xavier(w, w), xavier(w, 2)
            h = np.maximum(pts @ W1, 0)
            h = np.maximum(h @ W2, 0)
            vals.append(np.linalg.norm(h @ W3 - pts, axis=1).mean())
        print(f"{w:>8} {np.mean(vals):>18.4f}")
    null = np.linalg.norm(pts, axis=1).mean()
    print("-" * 28)
    print(f"{'f(x)=0':>8} {null:>18.4f}   <- a network that outputs nothing")
    print()
    print("The 'improvement' converges to the score of the zero function.")
    print("That is signal attenuation, not geometric coverage.")


def audit_diagonal_bug():
    print()
    print("=" * 70)
    print("3. relu_chain 1-D branch -- point[0] used as both x and y")
    print("=" * 70)
    rng = np.random.default_rng(1)
    pts = rng.normal(size=(2000, 2))
    intended = pts[:, 1]
    actual = pts[:, 0]
    print(f"intended y values: mean {intended.mean():+.3f}, "
          f"corr with x = {np.corrcoef(pts[:, 0], intended)[0, 1]:+.3f}")
    print(f"actual   y values: mean {actual.mean():+.3f}, "
          f"corr with x = {np.corrcoef(pts[:, 0], actual)[0, 1]:+.3f}")
    print()
    print("Correlation 1.000 means every point sits on the line y = x.")
    print("The 1-D results were measured against a diagonal, not a cloud.")


if __name__ == "__main__":
    audit_activation_count_metric()
    audit_output_decay_metric()
    audit_diagonal_bug()
    print()
    print("=" * 70)
    print("See docs/RESOLUTION.md. The corrected experiment is in")
    print("scripts/frequency_isolation.py.")
    print("=" * 70)
