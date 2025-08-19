import numpy as np
import matplotlib.pyplot as plt
import math
from utils import (
    count_activation_patterns,
    measure_true_geometric_distance,
    measure_region_quality,
    test_initialization_variance,
    measure_coverage,
)


if __name__ == "__main__":
    # Test the scaling
    neurons = [10, 20, 40, 80, 160]
    d = 3  # dimension
    m = 1000  # number of points

    print("=" * 60)
    print("NEURAL NETWORK COVERAGE ANALYSIS")
    print("=" * 60)

    avg_distances = []
    avg_patterns = []

    print("\n1. Basic Coverage Scaling:")
    for n in neurons:
        dist, patterns = measure_coverage(n, d, m)
        avg_distances.append(dist)
        avg_patterns.append(patterns)
        print(
            f"n={n}: avg_dist={dist:.3f}, patterns={patterns:.1f}, "
            f"theory_max={sum(math.comb(n,k) for k in range(d+1))}"
        )

    # Test initialization variance
    print("\n2. Testing Initialization Scale Effects:")
    widths = [20, 40, 80]
    init_scales = [0.1, 0.5, 1.0, 2.0, 5.0]
    init_results = test_initialization_variance(widths, init_scales)

    best_scale_per_width = {}
    for i, width in enumerate(widths):
        width_results = [
            (init_results["init_scale"][j], init_results["quality_score"][j])
            for j in range(len(init_results["width"]))
            if init_results["width"][j] == width
        ]
        best_scale, best_score = max(width_results, key=lambda x: x[1])
        best_scale_per_width[width] = best_scale
        print(
            f"Width {width}: Best init scale = {best_scale:.1f} (quality = {best_score:.3f})"
        )

    # Test geometric distance with true networks
    print("\n3. Testing True Geometric Distance:")
    geom_distances = []
    for n in [10, 20, 40]:
        W1 = np.random.randn(n, 1) * best_scale_per_width.get(n, 1.0)
        b1 = np.random.randn(n) * best_scale_per_width.get(n, 1.0)
        W2 = np.random.randn(1, n) * 0.1
        b2 = np.random.randn(1) * 0.1

        # Generate test points
        test_points = [
            (np.random.uniform(-2, 2), np.random.uniform(-2, 2)) for _ in range(100)
        ]

        geom_dist = measure_true_geometric_distance(W1, b1, W2, b2, test_points)
        geom_distances.append(geom_dist)
        print(f"Width {n}: Geometric distance = {geom_dist:.3f}")

    # Plot all results
    fig, axes = plt.subplots(2, 3, figsize=(18, 12))

    # Original scaling plots
    axes[0, 0].loglog(neurons, avg_distances, "o-", label="Measured")
    axes[0, 0].loglog(
        neurons, [n ** (-1 / d) for n in neurons], "--", label=f"n^(-1/{d})"
    )
    axes[0, 0].set_xlabel("Number of neurons")
    axes[0, 0].set_ylabel("Average distance")
    axes[0, 0].legend()
    axes[0, 0].set_title("Distance Scaling")
    axes[0, 0].grid(True, alpha=0.3)

    axes[0, 1].loglog(neurons, avg_patterns, "o-", label="Measured")
    theory = [min(sum(math.comb(n, k) for k in range(d + 1)), m) for n in neurons]
    axes[0, 1].loglog(neurons, theory, "--", label="Theory bound")
    axes[0, 1].set_xlabel("Number of neurons")
    axes[0, 1].set_ylabel("Number of activation patterns")
    axes[0, 1].legend()
    axes[0, 1].set_title("Pattern Count Scaling")
    axes[0, 1].grid(True, alpha=0.3)

    # Initialization scale effects
    for width in widths:
        width_data = [
            (init_results["init_scale"][i], init_results["quality_score"][i])
            for i in range(len(init_results["width"]))
            if init_results["width"][i] == width
        ]
        scales, scores = zip(*width_data)
        axes[0, 2].semilogx(scales, scores, "o-", label=f"Width {width}")
    axes[0, 2].set_xlabel("Initialization Scale")
    axes[0, 2].set_ylabel("Quality Score")
    axes[0, 2].set_title("Initialization Scale vs Quality")
    axes[0, 2].legend()
    axes[0, 2].grid(True, alpha=0.3)

    # Distance vs patterns
    for width in widths:
        width_data = [
            (init_results["n_patterns"][i], init_results["avg_distance"][i])
            for i in range(len(init_results["width"]))
            if init_results["width"][i] == width
        ]
        patterns, dists = zip(*width_data)
        axes[1, 0].scatter(patterns, dists, label=f"Width {width}", alpha=0.7)
    axes[1, 0].set_xlabel("Number of Patterns")
    axes[1, 0].set_ylabel("Average Distance")
    axes[1, 0].set_title("Patterns vs Distance Trade-off")
    axes[1, 0].legend()
    axes[1, 0].grid(True, alpha=0.3)

    # Geometric distance scaling
    if len(geom_distances) > 1:
        test_widths = [10, 20, 40]
        axes[1, 1].loglog(
            test_widths, geom_distances, "ro-", label="Geometric Distance"
        )
        axes[1, 1].set_xlabel("Network Width")
        axes[1, 1].set_ylabel("True Geometric Distance")
        axes[1, 1].set_title("True Geometric Distance Scaling")
        axes[1, 1].legend()
        axes[1, 1].grid(True, alpha=0.3)

    # Quality vs width
    width_quality = {}
    for i, width in enumerate(init_results["width"]):
        if width not in width_quality:
            width_quality[width] = []
        width_quality[width].append(init_results["quality_score"][i])

    widths_plot = sorted(width_quality.keys())
    avg_qualities = [np.mean(width_quality[w]) for w in widths_plot]
    std_qualities = [np.std(width_quality[w]) for w in widths_plot]

    axes[1, 2].errorbar(
        widths_plot, avg_qualities, yerr=std_qualities, fmt="go-", capsize=5
    )
    axes[1, 2].set_xlabel("Network Width")
    axes[1, 2].set_ylabel("Average Quality Score")
    axes[1, 2].set_title("Quality vs Network Width")
    axes[1, 2].grid(True, alpha=0.3)

    plt.suptitle("Neural Network Coverage Analysis: Complete Results", fontsize=16)
    plt.tight_layout()
    plt.savefig("./graphs/coverage_analysis_complete.png", dpi=300, bbox_inches="tight")
    plt.close()

    print("\n" + "=" * 60)
    print(
        "ANALYSIS COMPLETE - Results saved to ./graphs/coverage_analysis_complete.png"
    )
    print("=" * 60)
