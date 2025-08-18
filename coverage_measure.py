import numpy as np
import matplotlib.pyplot as plt
import math


def count_activation_patterns(W, b, X):
    """Count unique activation patterns for data X"""
    patterns = []
    for x in X:
        activations = (W @ x + b > 0).astype(int)
        patterns.append(tuple(activations))
    return len(set(patterns))


def relu_network(W1, b1, W2, b2, x):
    """Simple 2-layer ReLU network"""
    h = np.maximum(0, W1 @ x + b1)
    return W2 @ h + b2


def measure_true_geometric_distance(W1, b1, W2, b2, points):
    """Measure actual geometric distance to function graph"""
    distances = []
    for x_pt, y_pt in points:
        # Sample points on the function graph
        x_samples = np.linspace(-3, 3, 1000)
        y_samples = [relu_network(W1, b1, W2, b2, np.array([x])) for x in x_samples]
        y_samples = np.array(y_samples).flatten()

        # Find minimum distance
        dists = np.sqrt((x_samples - x_pt) ** 2 + (y_samples - y_pt) ** 2)
        distances.append(np.min(dists))

    return np.mean(distances)


def measure_region_quality(W, b, X):
    """Measure how well-positioned the regions are"""
    region_stats = {}

    for i, x in enumerate(X):
        # Get activation pattern for this point
        pattern = tuple((W @ x + b > 0).astype(int))

        if pattern not in region_stats:
            region_stats[pattern] = {"points": [], "indices": []}

        region_stats[pattern]["points"].append(x)
        region_stats[pattern]["indices"].append(i)

    quality_metrics = []

    for pattern, stats in region_stats.items():
        points = np.array(stats["points"])
        if len(points) > 1:
            # Compute region center
            center = np.mean(points, axis=0)

            # Compute average distance to center
            dists = [np.linalg.norm(p - center) for p in points]
            avg_dist_to_center = np.mean(dists)

            # Region compactness (lower is better)
            compactness = avg_dist_to_center / (len(points) ** (1 / len(center)))
            quality_metrics.append(
                {
                    "pattern": pattern,
                    "n_points": len(points),
                    "avg_dist_to_center": avg_dist_to_center,
                    "compactness": compactness,
                }
            )

    # Overall quality: balance between coverage and compactness
    if quality_metrics:
        avg_compactness = np.mean([m["compactness"] for m in quality_metrics])
        n_regions = len(quality_metrics)
        coverage_ratio = (
            len([m for m in quality_metrics if m["n_points"] > 1]) / n_regions
        )

        return {
            "avg_compactness": avg_compactness,
            "n_regions": n_regions,
            "coverage_ratio": coverage_ratio,
            "quality_score": coverage_ratio / (1 + avg_compactness),
        }

    return {
        "avg_compactness": np.inf,
        "n_regions": 0,
        "coverage_ratio": 0,
        "quality_score": 0,
    }


def test_initialization_variance(widths, init_scales, d=2, m=500, trials=20):
    """Test how initialization scale affects coverage"""
    results = {
        "width": [],
        "init_scale": [],
        "avg_distance": [],
        "n_patterns": [],
        "quality_score": [],
    }

    for width in widths:
        for scale in init_scales:
            distances = []
            pattern_counts = []
            quality_scores = []

            for _ in range(trials):
                # Initialize with specific scale
                W = np.random.randn(width, d) * scale
                b = np.random.randn(width) * scale

                # Random test points
                X = np.random.randn(m, d)

                # Count patterns
                n_patterns = count_activation_patterns(W, b, X)
                pattern_counts.append(n_patterns)

                # Measure quality
                quality = measure_region_quality(W, b, X)
                quality_scores.append(quality["quality_score"])

                # Measure distances (simplified)
                y = np.random.randn(m)
                min_dists = []
                for xi, yi in zip(X, y):
                    pattern = W @ xi + b > 0
                    dist = np.abs(yi - np.sum(pattern))
                    min_dists.append(dist)
                distances.append(np.mean(min_dists))

            results["width"].append(width)
            results["init_scale"].append(scale)
            results["avg_distance"].append(np.mean(distances))
            results["n_patterns"].append(np.mean(pattern_counts))
            results["quality_score"].append(np.mean(quality_scores))

    return results


def measure_coverage(n_neurons, d, m, trials=100):
    """Measure how activation patterns cover random points"""
    distances = []
    pattern_counts = []

    for _ in range(trials):
        # Random network
        W = np.random.randn(n_neurons, d)
        b = np.random.randn(n_neurons)

        # Random points
        X = np.random.randn(m, d)
        y = np.random.randn(m)

        # Count patterns
        n_patterns = count_activation_patterns(W, b, X)
        pattern_counts.append(n_patterns)

        # Measure distances (simplified - just using linear regions)
        min_dists = []
        for xi, yi in zip(X, y):
            # Find activation pattern for this point
            pattern = W @ xi + b > 0
            # In this region, function is linear
            # (simplified calculation for illustration)
            dist = np.abs(yi - np.sum(pattern))  # Simplified
            min_dists.append(dist)

        distances.append(np.mean(min_dists))

    return np.mean(distances), np.mean(pattern_counts)


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
