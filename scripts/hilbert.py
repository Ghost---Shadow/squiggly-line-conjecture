"""
Volume Coverage Optimization: Pure Test of the Squiggly Line Conjecture
Instead of training on a task, we directly optimize for spatial coverage
to see if Hilbert initialization provides better coverage than random init.
"""

import numpy as np
import torch
import torch.nn as nn
import matplotlib.pyplot as plt
from matplotlib import cm
from mpl_toolkits.mplot3d import Axes3D
import seaborn as sns
from scipy.spatial.distance import cdist
from typing import Tuple, List, Dict
import time
from collections import defaultdict

# Set style
plt.style.use("seaborn-v0_8-darkgrid")
sns.set_palette("husl")


def set_seed(seed=42):
    np.random.seed(seed)
    torch.manual_seed(seed)
    torch.cuda.manual_seed_all(seed)


# ============================================================================
# Hilbert Curve Implementation
# ============================================================================


def hilbert_curve_2d(order):
    """Generate 2D Hilbert curve points"""

    def hilbert_d2xy(n, d):
        x = y = 0
        s = 1
        while s < n:
            rx = 1 & (d // 2)
            ry = 1 & (d ^ rx)
            if ry == 0:
                if rx == 1:
                    x = s - 1 - x
                    y = s - 1 - y
                x, y = y, x
            x += s * rx
            y += s * ry
            d //= 4
            s *= 2
        return x, y

    n = 2**order
    points = []
    for d in range(n * n):
        x, y = hilbert_d2xy(n, d)
        points.append([x / (n - 1), y / (n - 1)])
    return np.array(points)


def hilbert_curve_3d(order):
    """Generate 3D Hilbert curve approximation"""
    # For 3D, we'll create a simple extension
    curve_2d = hilbert_curve_2d(order)
    n_points = len(curve_2d)
    z_coords = np.linspace(0, 1, n_points)

    # Create 3D curve by adding z dimension with oscillation
    curve_3d = np.zeros((n_points, 3))
    curve_3d[:, :2] = curve_2d
    curve_3d[:, 2] = z_coords * np.sin(np.linspace(0, 4 * np.pi, n_points)) * 0.5 + 0.5

    return curve_3d


# ============================================================================
# Network Architectures for Coverage Testing
# ============================================================================


class CoverageNetwork(nn.Module):
    """Base class for networks we'll test for spatial coverage"""

    def __init__(self, input_dim=2, hidden_dims=[64, 64], output_dim=1):
        super().__init__()
        self.input_dim = input_dim
        self.layers = nn.ModuleList()

        dims = [input_dim] + hidden_dims + [output_dim]
        for i in range(len(dims) - 1):
            self.layers.append(nn.Linear(dims[i], dims[i + 1]))

    def forward(self, x):
        for i, layer in enumerate(self.layers[:-1]):
            x = torch.relu(layer(x))
        return self.layers[-1](x)

    def get_activation_pattern(self, x):
        """Get binary activation pattern for ReLU neurons"""
        patterns = []
        with torch.no_grad():
            for i, layer in enumerate(self.layers[:-1]):
                x = layer(x)
                pattern = (x > 0).float()
                patterns.append(pattern)
                x = torch.relu(x)
        return torch.cat(patterns, dim=1)


class RandomNetwork(CoverageNetwork):
    """Standard random initialization (Xavier/Glorot)"""

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.apply(self._init_weights)

    def _init_weights(self, module):
        if isinstance(module, nn.Linear):
            nn.init.xavier_uniform_(module.weight)
            if module.bias is not None:
                nn.init.zeros_(module.bias)


class HilbertNetwork(CoverageNetwork):
    """Hilbert curve-based initialization"""

    def __init__(self, *args, hilbert_order=5, **kwargs):
        super().__init__(*args, **kwargs)
        self.hilbert_order = hilbert_order
        self._hilbert_init()

    def _hilbert_init(self):
        """Initialize weights using Hilbert curve structure"""
        # Generate Hilbert curve
        if self.input_dim == 2:
            curve = hilbert_curve_2d(self.hilbert_order)
        else:
            curve = hilbert_curve_3d(self.hilbert_order)

        curve = 2 * curve - 1  # Scale to [-1, 1]

        for layer_idx, layer in enumerate(self.layers):
            in_features = layer.in_features
            out_features = layer.out_features

            # Create weight matrix using Hilbert curve
            W = np.zeros((out_features, in_features))

            # Sample points along Hilbert curve for each neuron
            n_samples = max(out_features, in_features)
            indices = np.linspace(0, len(curve) - 1, n_samples, dtype=int)
            sampled_curve = curve[indices]

            for i in range(out_features):
                for j in range(in_features):
                    # Use curve geometry to set weights
                    i_idx = int(i * len(sampled_curve) / out_features)
                    j_idx = int(j * len(sampled_curve) / in_features)

                    # Weight based on curve proximity
                    if self.input_dim == 2:
                        W[i, j] = np.sin(
                            4
                            * np.pi
                            * np.linalg.norm(
                                sampled_curve[i_idx] - sampled_curve[j_idx]
                            )
                        )
                    else:
                        # For higher dimensions, use dot product
                        W[i, j] = np.tanh(
                            np.dot(
                                sampled_curve[i_idx % len(sampled_curve)],
                                sampled_curve[j_idx % len(sampled_curve)],
                            )
                        )

            # Normalize
            W = W * np.sqrt(2.0 / in_features)
            layer.weight.data = torch.FloatTensor(W)

            if layer.bias is not None:
                # Bias follows curve too
                bias_indices = np.linspace(0, len(curve) - 1, out_features, dtype=int)
                bias_values = curve[bias_indices].mean(axis=1) * 0.1
                layer.bias.data = torch.FloatTensor(bias_values)


class SpiralNetwork(CoverageNetwork):
    """Spiral/Sinusoidal initialization for comparison"""

    def __init__(self, *args, frequency=5, **kwargs):
        super().__init__(*args, **kwargs)
        self.frequency = frequency
        self._spiral_init()

    def _spiral_init(self):
        """Initialize with spiral/sinusoidal pattern"""
        for layer in self.layers:
            in_features = layer.in_features
            out_features = layer.out_features

            # Create spiral pattern
            W = np.zeros((out_features, in_features))
            for i in range(out_features):
                for j in range(in_features):
                    phase_i = 2 * np.pi * i / out_features
                    phase_j = 2 * np.pi * j / in_features
                    W[i, j] = np.sin(self.frequency * phase_i) * np.cos(
                        self.frequency * phase_j
                    )

            W = W * np.sqrt(2.0 / in_features)
            layer.weight.data = torch.FloatTensor(W)

            if layer.bias is not None:
                nn.init.zeros_(layer.bias)


# ============================================================================
# Coverage Metrics
# ============================================================================


def compute_coverage_metrics(network, test_points, epsilon=0.1):
    """Compute various coverage metrics for a network"""

    network.eval()
    device = next(network.parameters()).device
    test_points_tensor = torch.FloatTensor(test_points).to(device)

    with torch.no_grad():
        # Get network outputs
        outputs = network(test_points_tensor).cpu().numpy()

        # Get activation patterns
        patterns = network.get_activation_pattern(test_points_tensor).cpu().numpy()

    # Combine input and output for full space
    if len(outputs.shape) == 1:
        outputs = outputs.reshape(-1, 1)
    full_points = np.concatenate([test_points, outputs], axis=1)

    metrics = {}

    # 1. Number of unique activation patterns (complexity)
    unique_patterns = np.unique(patterns, axis=0)
    metrics["n_patterns"] = len(unique_patterns)

    # 2. Average minimum distance to random points
    n_random = 1000
    if test_points.shape[1] == 2:
        random_points = np.random.uniform(-1, 1, (n_random, 3))  # 2D input + 1D output
    else:
        random_points = np.random.uniform(-1, 1, (n_random, 4))  # 3D input + 1D output

    # For each random point, find closest point on network surface
    distances = cdist(random_points, full_points, metric="euclidean")
    min_distances = np.min(distances, axis=1)

    metrics["avg_min_distance"] = np.mean(min_distances)
    metrics["std_min_distance"] = np.std(min_distances)
    metrics["max_min_distance"] = np.max(min_distances)

    # 3. Coverage ratio (% of random points within epsilon)
    metrics["coverage_ratio"] = np.mean(min_distances < epsilon)

    # 4. Effective volume covered (approximate)
    # Count grid cells that have at least one point
    grid_size = 20
    if test_points.shape[1] == 2:
        grid = np.zeros((grid_size, grid_size, grid_size))
        for point in full_points:
            i = int((point[0] + 1) * grid_size / 2)
            j = int((point[1] + 1) * grid_size / 2)
            k = int((point[2] + 1) * grid_size / 2)
            if 0 <= i < grid_size and 0 <= j < grid_size and 0 <= k < grid_size:
                grid[i, j, k] = 1
    else:
        # For 3D input, use 4D grid (more approximate)
        grid = np.zeros((grid_size, grid_size, grid_size, grid_size // 2))
        for point in full_points:
            i = int((point[0] + 1) * grid_size / 2)
            j = int((point[1] + 1) * grid_size / 2)
            k = int((point[2] + 1) * grid_size / 2)
            l = int((point[3] + 1) * grid_size / 4)
            if (
                0 <= i < grid_size
                and 0 <= j < grid_size
                and 0 <= k < grid_size
                and 0 <= l < grid_size // 2
            ):
                grid[i, j, k, l] = 1

    metrics["volume_coverage"] = np.sum(grid) / grid.size

    # 5. Path length (approximate arc length of function)
    sorted_indices = np.argsort(test_points[:, 0])
    sorted_full_points = full_points[sorted_indices]
    path_length = np.sum(np.linalg.norm(np.diff(sorted_full_points, axis=0), axis=1))
    metrics["path_length"] = path_length

    return metrics


# ============================================================================
# Visualization Functions
# ============================================================================


def visualize_2d_coverage(networks, names, test_density=100):
    """Visualize 2D function coverage"""

    fig = plt.figure(figsize=(16, 12))

    # Create test grid
    x = np.linspace(-1, 1, test_density)
    y = np.linspace(-1, 1, test_density)
    X, Y = np.meshgrid(x, y)
    test_points = np.column_stack([X.ravel(), Y.ravel()])

    n_networks = len(networks)

    for idx, (network, name) in enumerate(zip(networks, names)):
        network.eval()

        # Get network outputs
        with torch.no_grad():
            inputs = torch.FloatTensor(test_points)
            outputs = network(inputs).numpy().reshape(test_density, test_density)

            # Get activation patterns
            patterns = network.get_activation_pattern(inputs).numpy()
            unique_patterns = np.unique(patterns, axis=0)

        # 1. Function surface
        ax1 = fig.add_subplot(3, n_networks, idx + 1, projection="3d")
        ax1.plot_surface(X, Y, outputs, cmap="viridis", alpha=0.8)
        ax1.set_title(f"{name}\nFunction Surface")
        ax1.set_xlabel("X")
        ax1.set_ylabel("Y")
        ax1.set_zlabel("Output")

        # 2. Contour plot
        ax2 = fig.add_subplot(3, n_networks, n_networks + idx + 1)
        contour = ax2.contourf(X, Y, outputs, levels=20, cmap="viridis")
        ax2.set_title(f"Contour Plot\n{len(unique_patterns)} patterns")
        ax2.set_xlabel("X")
        ax2.set_ylabel("Y")
        plt.colorbar(contour, ax=ax2)

        # 3. Activation pattern regions
        ax3 = fig.add_subplot(3, n_networks, 2 * n_networks + idx + 1)

        # Convert patterns to unique IDs for visualization
        pattern_ids = np.zeros(len(patterns))
        for i, pattern in enumerate(patterns):
            for j, unique_pattern in enumerate(unique_patterns):
                if np.array_equal(pattern, unique_pattern):
                    pattern_ids[i] = j
                    break

        pattern_grid = pattern_ids.reshape(test_density, test_density)
        im = ax3.imshow(
            pattern_grid, cmap="tab20", origin="lower", extent=[-1, 1, -1, 1]
        )
        ax3.set_title(f"Activation Regions")
        ax3.set_xlabel("X")
        ax3.set_ylabel("Y")

    plt.suptitle(
        "2D Coverage Comparison: Network Initialization Strategies", fontsize=16
    )
    plt.tight_layout()

    return fig


def plot_coverage_metrics(all_metrics, dimensions=[2, 3]):
    """Plot comprehensive coverage metrics comparison"""

    fig = plt.figure(figsize=(16, 10))

    metric_names = [
        "avg_min_distance",
        "coverage_ratio",
        "n_patterns",
        "volume_coverage",
        "path_length",
    ]
    metric_labels = [
        "Avg Min Distance\n(Lower is Better)",
        "Coverage Ratio\n(Higher is Better)",
        "Unique Patterns\n(Higher = More Complex)",
        "Volume Coverage\n(Higher is Better)",
        "Path Length\n(Higher = More Squiggly)",
    ]

    for dim_idx, dim in enumerate(dimensions):
        for metric_idx, (metric_name, metric_label) in enumerate(
            zip(metric_names, metric_labels)
        ):
            ax = fig.add_subplot(
                len(dimensions),
                len(metric_names),
                dim_idx * len(metric_names) + metric_idx + 1,
            )

            # Prepare data for plotting
            data = []
            labels = []
            colors = []
            color_map = {"Random": "blue", "Hilbert": "red", "Spiral": "green"}

            for init_type in ["Random", "Hilbert", "Spiral"]:
                key = f"{init_type}_{dim}D"
                if key in all_metrics:
                    values = [run[metric_name] for run in all_metrics[key]]
                    data.append(values)
                    labels.append(init_type)
                    colors.append(color_map[init_type])

            # Create box plot
            bp = ax.boxplot(data, labels=labels, patch_artist=True)
            for patch, color in zip(bp["boxes"], colors):
                patch.set_facecolor(color)
                patch.set_alpha(0.6)

            ax.set_ylabel(metric_label)
            if dim_idx == 0:
                ax.set_title(f"{metric_label.split(chr(10))[0]}")

            if metric_idx == 0:
                ax.text(
                    -0.3,
                    0.5,
                    f"{dim}D Space",
                    transform=ax.transAxes,
                    rotation=90,
                    va="center",
                    fontsize=12,
                    fontweight="bold",
                )

            ax.grid(True, alpha=0.3)

    plt.suptitle(
        "Coverage Metrics: Hilbert vs Random vs Spiral Initialization",
        fontsize=16,
        fontweight="bold",
    )
    plt.tight_layout()

    return fig


# ============================================================================
# Main Experimental Framework
# ============================================================================


def run_coverage_experiment(
    input_dim=2, hidden_dims=[64, 64], n_runs=10, n_test_points=10000, hilbert_order=5
):
    """Run coverage comparison experiment"""

    print(f"\n{'='*60}")
    print(f"Testing {input_dim}D Space Coverage")
    print(f"{'='*60}")

    # Generate dense test points
    if input_dim == 2:
        # 2D grid
        grid_size = int(np.sqrt(n_test_points))
        x = np.linspace(-1, 1, grid_size)
        y = np.linspace(-1, 1, grid_size)
        X, Y = np.meshgrid(x, y)
        test_points = np.column_stack([X.ravel(), Y.ravel()])
    else:
        # 3D grid
        grid_size = int(n_test_points ** (1 / 3))
        x = np.linspace(-1, 1, grid_size)
        y = np.linspace(-1, 1, grid_size)
        z = np.linspace(-1, 1, grid_size)
        X, Y, Z = np.meshgrid(x, y, z)
        test_points = np.column_stack([X.ravel(), Y.ravel(), Z.ravel()])

    # Storage for results
    results = defaultdict(list)

    for run in range(n_runs):
        set_seed(42 + run)

        # Create networks
        networks = {
            "Random": RandomNetwork(input_dim=input_dim, hidden_dims=hidden_dims),
            "Hilbert": HilbertNetwork(
                input_dim=input_dim,
                hidden_dims=hidden_dims,
                hilbert_order=hilbert_order,
            ),
            "Spiral": SpiralNetwork(input_dim=input_dim, hidden_dims=hidden_dims),
        }

        # Compute metrics for each network
        for name, network in networks.items():
            metrics = compute_coverage_metrics(network, test_points)
            results[f"{name}_{input_dim}D"].append(metrics)

            if run == 0:  # Print first run results
                print(f"\n{name} Network:")
                print(f"  Avg Min Distance: {metrics['avg_min_distance']:.4f}")
                print(f"  Coverage Ratio: {metrics['coverage_ratio']:.4f}")
                print(f"  Unique Patterns: {metrics['n_patterns']}")
                print(f"  Volume Coverage: {metrics['volume_coverage']:.4f}")
                print(f"  Path Length: {metrics['path_length']:.2f}")

    return results, networks, test_points


def main():
    """Run complete coverage analysis"""

    print("=" * 60)
    print("VOLUME COVERAGE OPTIMIZATION TEST")
    print("Pure Test of the Squiggly Line Conjecture")
    print("=" * 60)

    # Parameters
    params = {
        "hidden_dims": [64, 64],
        "n_runs": 10,
        "n_test_points": 10000,
        "hilbert_order": 5,
    }

    print("\nExperimental Parameters:")
    for key, value in params.items():
        print(f"  {key}: {value}")

    all_results = {}

    # Test in 2D and 3D
    for dim in [2, 3]:
        results, networks, test_points = run_coverage_experiment(
            input_dim=dim, **params
        )
        all_results.update(results)

        # Visualize 2D case
        if dim == 2:
            print("\nGenerating 2D visualizations...")
            fig_2d = visualize_2d_coverage(
                list(networks.values()), list(networks.keys()), test_density=50
            )

            # Save 2D visualization
            import os

            save_dir = "../graphs"
            os.makedirs(save_dir, exist_ok=True)

            from datetime import datetime

            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

            filepath = os.path.join(save_dir, f"coverage_2d_comparison_{timestamp}.png")
            fig_2d.savefig(filepath, dpi=300, bbox_inches="tight")
            print(f"2D visualization saved to: {filepath}")
            plt.close(fig_2d)

    # Plot comprehensive metrics
    print("\nGenerating metrics comparison...")
    fig_metrics = plot_coverage_metrics(all_results, dimensions=[2, 3])

    # Save metrics plot
    filepath = os.path.join(save_dir, f"coverage_metrics_{timestamp}.png")
    fig_metrics.savefig(filepath, dpi=300, bbox_inches="tight")
    print(f"Metrics plot saved to: {filepath}")

    # Also save latest versions
    fig_metrics.savefig(
        os.path.join(save_dir, "coverage_metrics_latest.png"),
        dpi=300,
        bbox_inches="tight",
    )
    plt.close(fig_metrics)

    # Statistical Analysis
    print("\n" + "=" * 60)
    print("STATISTICAL ANALYSIS")
    print("=" * 60)

    from scipy import stats

    for dim in [2, 3]:
        print(f"\n{dim}D Space Results:")

        # Compare Hilbert vs Random on key metric (avg_min_distance)
        hilbert_distances = [
            r["avg_min_distance"] for r in all_results[f"Hilbert_{dim}D"]
        ]
        random_distances = [
            r["avg_min_distance"] for r in all_results[f"Random_{dim}D"]
        ]

        t_stat, p_value = stats.ttest_ind(hilbert_distances, random_distances)

        print(f"\n  Average Minimum Distance (Hilbert vs Random):")
        print(
            f"    Hilbert: {np.mean(hilbert_distances):.4f} ± {np.std(hilbert_distances):.4f}"
        )
        print(
            f"    Random:  {np.mean(random_distances):.4f} ± {np.std(random_distances):.4f}"
        )
        print(f"    t-statistic: {t_stat:.3f}")
        print(f"    p-value: {p_value:.6f}")
        print(f"    Significant: {'Yes' if p_value < 0.05 else 'No'}")

        # Coverage ratio comparison
        hilbert_coverage = [r["coverage_ratio"] for r in all_results[f"Hilbert_{dim}D"]]
        random_coverage = [r["coverage_ratio"] for r in all_results[f"Random_{dim}D"]]

        print(f"\n  Coverage Ratio (Hilbert vs Random):")
        print(
            f"    Hilbert: {np.mean(hilbert_coverage):.4f} ± {np.std(hilbert_coverage):.4f}"
        )
        print(
            f"    Random:  {np.mean(random_coverage):.4f} ± {np.std(random_coverage):.4f}"
        )

        # Path length comparison
        hilbert_path = [r["path_length"] for r in all_results[f"Hilbert_{dim}D"]]
        random_path = [r["path_length"] for r in all_results[f"Random_{dim}D"]]

        print(f"\n  Path Length (Squiggliness):")
        print(f"    Hilbert: {np.mean(hilbert_path):.2f} ± {np.std(hilbert_path):.2f}")
        print(f"    Random:  {np.mean(random_path):.2f} ± {np.std(random_path):.2f}")

    print("\n" + "=" * 60)
    print("CONCLUSION")
    print("=" * 60)

    # Determine overall results
    hilbert_wins_2d = np.mean(
        [r["avg_min_distance"] for r in all_results["Hilbert_2D"]]
    ) < np.mean([r["avg_min_distance"] for r in all_results["Random_2D"]])
    hilbert_wins_3d = np.mean(
        [r["avg_min_distance"] for r in all_results["Hilbert_3D"]]
    ) < np.mean([r["avg_min_distance"] for r in all_results["Random_3D"]])

    if hilbert_wins_2d and hilbert_wins_3d:
        print("\n✓ Hilbert initialization CONFIRMS better spatial coverage!")
        print("  - Lower average distance to random points in space")
        print("  - Systematic coverage beats random initialization")
        print("  - The Squiggly Line Conjecture holds for designed curves!")
    elif hilbert_wins_2d or hilbert_wins_3d:
        print("\n⚬ Mixed results: Hilbert wins in some dimensions")
        print("  - May depend on specific architecture or dimension")
    else:
        print("\n✗ Random initialization performs comparably or better")
        print("  - Designed coverage doesn't guarantee improvement")

    print("\nKey Insight: The experiment directly tests whether systematic")
    print("space-filling (Hilbert) provides better coverage than random")
    print("initialization, independent of any specific learning task.")

    return all_results


if __name__ == "__main__":
    results = main()
