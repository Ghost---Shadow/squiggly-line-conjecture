import numpy as np
import matplotlib.pyplot as plt


def count_activation_patterns(W, b, X):
    """Count unique activation patterns for data X"""
    patterns = []
    for x in X:
        activations = (W @ x + b > 0).astype(int)
        patterns.append(tuple(activations))
    return len(set(patterns))


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


# Test the scaling
neurons = [10, 20, 40, 80, 160]
d = 3  # dimension
m = 1000  # number of points

avg_distances = []
avg_patterns = []

for n in neurons:
    dist, patterns = measure_coverage(n, d, m)
    avg_distances.append(dist)
    avg_patterns.append(patterns)
    print(
        f"n={n}: avg_dist={dist:.3f}, patterns={patterns:.1f}, "
        f"theory_max={sum(np.math.comb(n,k) for k in range(d+1))}"
    )

# Plot scaling
plt.figure(figsize=(12, 5))
plt.subplot(1, 2, 1)
plt.loglog(neurons, avg_distances, "o-", label="Measured")
plt.loglog(neurons, [n ** (-1 / d) for n in neurons], "--", label=f"n^(-1/{d})")
plt.xlabel("Number of neurons")
plt.ylabel("Average distance")
plt.legend()
plt.title("Distance Scaling")

plt.subplot(1, 2, 2)
plt.loglog(neurons, avg_patterns, "o-", label="Measured")
theory = [min(sum(np.math.comb(n, k) for k in range(d + 1)), m) for n in neurons]
plt.loglog(neurons, theory, "--", label="Theory bound")
plt.xlabel("Number of neurons")
plt.ylabel("Number of activation patterns")
plt.legend()
plt.title("Pattern Count Scaling")
plt.tight_layout()
plt.savefig("./graphs/coverage_measure.png", dpi=300, bbox_inches="tight")
plt.close()
