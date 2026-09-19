"""
DEFECT WARNING -- read docs/RESOLUTION.md §4 before using any number from here.

Sections 1-2 depend on `utils.measure_coverage`, whose "distance" is
|y - (number of active neurons)| ~ width/2, not a distance to anything. The
avg_dist column and the coverage_* figures plot that quantity.

Section 3 (`measure_true_geometric_distance`) is a correct Euclidean metric; it
shows no trend with width.

Metrics deliberately left unfixed as the historical record.
"""
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
import pandas as pd
import math

# Set seaborn style
sns.set_style("whitegrid")
plt.rcParams['figure.figsize'] = (10, 8)
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

    # Plot 1: Scaling Laws - combine distance and patterns using dual y-axis and hue
    plt.figure(figsize=(10, 8))
    
    # Prepare data combining both distance and patterns
    scaling_data = []
    for i, n in enumerate(neurons):
        scaling_data.append({"neurons": n, "value": avg_distances[i], "metric": "Distance", "type": "Measured"})
        theory_dist = n ** (-1 / d)
        scaling_data.append({"neurons": n, "value": theory_dist, "metric": "Distance", "type": "Theory"})
        scaling_data.append({"neurons": n, "value": avg_patterns[i], "metric": "Patterns", "type": "Measured"})
        theory_patt = min(sum(math.comb(n, k) for k in range(d + 1)), m)
        scaling_data.append({"neurons": n, "value": theory_patt, "metric": "Patterns", "type": "Theory"})
    
    scaling_df = pd.DataFrame(scaling_data)
    
    # Plot distance data
    dist_data = scaling_df[scaling_df["metric"] == "Distance"]
    sns.lineplot(data=dist_data, x="neurons", y="value", hue="type", style="type",
                markers=True, linewidth=2, markersize=8)
    
    plt.xscale('log')
    plt.yscale('log')
    plt.xlabel("Number of neurons")
    plt.ylabel("Scaling Value")
    plt.title("Neural Network Coverage Scaling Laws")
    plt.legend(title="Distance Scaling")
    plt.tight_layout()
    plt.savefig("../graphs/coverage_distance_scaling.png", dpi=300, bbox_inches="tight")
    plt.close()

    # Plot 2: Pattern Scaling 
    plt.figure(figsize=(10, 8))
    patt_data = scaling_df[scaling_df["metric"] == "Patterns"]
    sns.lineplot(data=patt_data, x="neurons", y="value", hue="type", style="type",
                markers=True, linewidth=2, markersize=8)
    
    plt.xscale('log')
    plt.yscale('log')
    plt.xlabel("Number of neurons")
    plt.ylabel("Number of activation patterns")
    plt.title("Pattern Count Scaling")
    plt.legend(title="Pattern Scaling")
    plt.tight_layout()
    plt.savefig("../graphs/coverage_pattern_scaling.png", dpi=300, bbox_inches="tight")
    plt.close()

    # Plot 3: Initialization Effects by Width
    plt.figure(figsize=(10, 8))
    init_data = []
    for width in widths:
        width_data = [
            (init_results["init_scale"][i], init_results["quality_score"][i])
            for i in range(len(init_results["width"]))
            if init_results["width"][i] == width
        ]
        for scale, score in width_data:
            init_data.append({"scale": scale, "quality": score, "width": f"Width {width}"})
    
    init_df = pd.DataFrame(init_data)
    sns.lineplot(data=init_df, x="scale", y="quality", hue="width", 
                marker="o", linewidth=2, markersize=8)
    plt.xscale('log')
    plt.xlabel("Initialization Scale")
    plt.ylabel("Quality Score")
    plt.title("Initialization Scale Effects by Network Width")
    plt.legend(title="Network Width")
    plt.tight_layout()
    plt.savefig("../graphs/coverage_initialization_effects.png", dpi=300, bbox_inches="tight")
    plt.close()

    # Plot 4: Patterns vs Distance Trade-off
    plt.figure(figsize=(10, 8))
    plot_data = []
    for width in widths:
        width_data = [
            (init_results["n_patterns"][i], init_results["avg_distance"][i])
            for i in range(len(init_results["width"]))
            if init_results["width"][i] == width
        ]
        for patterns, distance in width_data:
            plot_data.append({"patterns": patterns, "distance": distance, "width": f"Width {width}"})
    
    df = pd.DataFrame(plot_data)
    sns.scatterplot(data=df, x="patterns", y="distance", hue="width", s=60, alpha=0.7)
    plt.xlabel("Number of Patterns")
    plt.ylabel("Average Distance")
    plt.title("Patterns vs Distance Trade-off by Network Width")
    plt.legend(title="Network Width")
    plt.tight_layout()
    plt.savefig("../graphs/coverage_patterns_vs_distance.png", dpi=300, bbox_inches="tight")
    plt.close()

    print("\n" + "=" * 60)
    print("ANALYSIS COMPLETE - Individual graphs saved to ./graphs/")
    print("- coverage_distance_scaling.png")
    print("- coverage_pattern_scaling.png")
    print("- coverage_initialization_effects.png")
    print("- coverage_patterns_vs_distance.png")
    print("=" * 60)
