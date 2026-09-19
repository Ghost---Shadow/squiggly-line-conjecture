"""
DEFECT WARNING -- read docs/RESOLUTION.md §4 before using any number from here.

`measure_coverage` does not measure a distance. Its inner loop computes

    dist = np.abs(yi - np.sum(pattern))

where `pattern` is the boolean activation vector, so `np.sum(pattern)` is the
COUNT OF ACTIVE NEURONS (~ width/2). The returned "avg distance" therefore grows
linearly with width and is independent of the data.

Deliberately left unfixed: this is the historical record the audit depends on,
and scripts/audit_legacy_metrics.py imports it directly to reproduce the defect.
`measure_true_geometric_distance` is a genuine Euclidean metric and is unaffected.
"""
import numpy as np
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


def generate_data_distribution(distribution, n_points, d):
    """Generate data from different distributions"""
    np.random.seed(42)

    if distribution == "uniform":
        return np.random.uniform(-2, 2, (n_points, d))
    elif distribution == "gaussian":
        return np.random.randn(n_points, d)
    elif distribution == "clusters":
        # Generate clustered data
        n_clusters = 3
        cluster_size = n_points // n_clusters
        data = []
        for i in range(n_clusters):
            center = np.random.uniform(-3, 3, d)
            cluster = np.random.randn(cluster_size, d) * 0.5 + center
            data.append(cluster)
        remaining = n_points - n_clusters * cluster_size
        if remaining > 0:
            center = np.random.uniform(-3, 3, d)
            cluster = np.random.randn(remaining, d) * 0.5 + center
            data.append(cluster)
        return np.vstack(data)
    elif distribution == "manifold":
        # Generate data on a low-dimensional manifold
        if d >= 2:
            t = np.random.uniform(0, 2 * np.pi, n_points)
            manifold_data = np.column_stack([np.cos(t), np.sin(t)])
            # Add noise in remaining dimensions
            if d > 2:
                noise = np.random.randn(n_points, d - 2) * 0.1
                return np.column_stack([manifold_data, noise])
            return manifold_data
        else:
            return np.random.randn(n_points, d)
    else:
        raise ValueError(f"Unknown distribution: {distribution}")


def create_deep_network(layer_sizes):
    """Create a deep ReLU network with given layer sizes"""
    weights = []
    biases = []

    for i in range(len(layer_sizes) - 1):
        W = np.random.randn(layer_sizes[i + 1], layer_sizes[i]) / np.sqrt(
            layer_sizes[i]
        )
        b = np.zeros(layer_sizes[i + 1])
        weights.append(W)
        biases.append(b)

    return weights, biases


def forward_deep_network(weights, biases, x):
    """Forward pass through deep network"""
    h = x
    for i, (W, b) in enumerate(zip(weights, biases)):
        h = W @ h + b
        if i < len(weights) - 1:  # Don't apply ReLU to output
            h = np.maximum(0, h)
    return h
