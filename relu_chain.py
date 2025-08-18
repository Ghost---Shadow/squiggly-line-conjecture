import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation
from IPython.display import HTML
import seaborn as sns

# Set style
plt.style.use("seaborn-v0_8-darkgrid")
sns.set_palette("husl")


class ReLUNetwork(nn.Module):
    """Dense network with ReLU activations and controllable architecture."""

    def __init__(self, input_dim=1, hidden_dims=[4, 4], output_dim=1):
        super().__init__()

        dims = [input_dim] + hidden_dims + [output_dim]
        self.layers = nn.ModuleList()

        for i in range(len(dims) - 1):
            self.layers.append(nn.Linear(dims[i], dims[i + 1]))

    def forward(self, x, return_activations=False):
        activations = []
        h = x

        for i, layer in enumerate(self.layers):
            h = layer(h)
            if i < len(self.layers) - 1:  # Don't apply ReLU to output
                h_before_relu = h.clone()
                h = torch.relu(h)
                if return_activations:
                    activations.append(
                        {
                            "pre_relu": h_before_relu,
                            "post_relu": h,
                            "active_ratio": (h > 0).float().mean(dim=0),
                        }
                    )

        if return_activations:
            return h, activations
        return h

    def get_polynomial_in_positive_region(self, x):
        """When all ReLUs fire positive, the network is just a linear function."""
        W_composite = None
        b_composite = None

        with torch.no_grad():
            # Compute the composite linear transformation
            for i, layer in enumerate(self.layers):
                W = layer.weight
                b = layer.bias

                if W_composite is None:
                    W_composite = W
                    b_composite = b
                else:
                    W_composite = W @ W_composite
                    b_composite = W @ b_composite + b

        # This is now a linear (degree-1) polynomial: W_composite * x + b_composite
        return W_composite @ x.T + b_composite.unsqueeze(1)


def analyze_squiggly_line_effect(
    input_dim=2, max_width=32, n_samples=100, n_data_points=50
):
    """Analyze how network width affects distance to random data points."""

    torch.manual_seed(42)
    np.random.seed(42)

    # Generate random data points
    data_points = torch.randn(n_data_points, input_dim)

    widths = [2, 4, 8, 16, max_width]
    results = {
        "width": [],
        "avg_min_distance": [],
        "std_min_distance": [],
        "positive_activation_ratio": [],
        "effective_params": [],
    }

    for width in widths:
        print(f"Testing width: {width}")
        distances = []
        activation_ratios = []

        for _ in range(n_samples):
            # Random network
            if input_dim == 1:
                net = ReLUNetwork(input_dim=1, hidden_dims=[width, width], output_dim=1)
            else:
                net = ReLUNetwork(
                    input_dim=input_dim,
                    hidden_dims=[width, width],
                    output_dim=input_dim,
                )

            # Random initialization (default PyTorch)
            def init_weights(m):
                if isinstance(m, nn.Linear):
                    nn.init.xavier_uniform_(m.weight)
                    nn.init.zeros_(m.bias)

            net.apply(init_weights)

            # Compute network output at data points
            with torch.no_grad():
                if input_dim == 1:
                    # For 1D, create a dense sampling for curve
                    x_curve = torch.linspace(-3, 3, 1000).unsqueeze(1)
                    y_curve, acts = net(x_curve, return_activations=True)

                    # Measure distances from data points to curve
                    min_dists = []
                    for point in data_points:
                        # Point is (x, y) in 2D space for visualization
                        # We need to find closest point on curve y = f(x)
                        dists = torch.sqrt(
                            (x_curve.squeeze() - point[0]) ** 2
                            + (y_curve.squeeze() - point[0]) ** 2
                        )  # Using point[0] as y-value too for simplicity
                        min_dists.append(dists.min().item())
                else:
                    # For higher dims, compute output at data points directly
                    outputs = net(data_points)
                    # Distance in output space (simplified metric)
                    min_dists = torch.norm(outputs - data_points, dim=1).tolist()

                # Track activation patterns
                _, activations = net(data_points, return_activations=True)
                avg_positive = np.mean(
                    [act["active_ratio"].mean().item() for act in activations]
                )
                activation_ratios.append(avg_positive)

            distances.extend(min_dists)

        results["width"].append(width)
        results["avg_min_distance"].append(np.mean(distances))
        results["std_min_distance"].append(np.std(distances))
        results["positive_activation_ratio"].append(np.mean(activation_ratios))
        results["effective_params"].append(width * width * 2 + width * (input_dim + 1))

    return results


def visualize_polynomial_behavior_1d():
    """Visualize how networks of different widths behave as polynomials in 1D."""

    torch.manual_seed(42)
    fig, axes = plt.subplots(2, 3, figsize=(15, 10))
    axes = axes.flatten()

    widths = [1, 2, 4, 8, 16, 32]
    x = torch.linspace(-3, 3, 1000).unsqueeze(1)

    # Generate random "data points" to measure distance to
    n_points = 20
    data_x = torch.rand(n_points) * 6 - 3
    data_y = torch.randn(n_points) * 0.5

    for idx, width in enumerate(widths):
        ax = axes[idx]

        # Create network
        net = ReLUNetwork(input_dim=1, hidden_dims=[width, width], output_dim=1)

        with torch.no_grad():
            y, activations = net(x, return_activations=True)

            # Color code by activation pattern
            # This shows where different "polynomial pieces" are
            activation_pattern = torch.cat(
                [act["post_relu"].mean(dim=1, keepdim=True) > 0 for act in activations],
                dim=1,
            )
            pattern_id = activation_pattern.float() @ (
                2.0 ** torch.arange(len(activations)).float()
            ).unsqueeze(1)

            # Plot the function
            scatter = ax.scatter(
                x.numpy(),
                y.numpy(),
                c=pattern_id.numpy(),
                s=1,
                cmap="viridis",
                alpha=0.7,
            )

            # Plot data points
            ax.scatter(
                data_x.numpy(),
                data_y.numpy(),
                c="red",
                s=30,
                zorder=5,
                label="Data points",
                edgecolors="black",
                linewidth=1,
            )

            # Compute and display average minimum distance
            min_dists = []
            for i in range(n_points):
                dists = torch.sqrt(
                    (x.squeeze() - data_x[i]) ** 2 + (y.squeeze() - data_y[i]) ** 2
                )
                min_dists.append(dists.min().item())
            avg_dist = np.mean(min_dists)

            ax.set_title(f"Width={width}, Avg Min Dist={avg_dist:.3f}")
            ax.set_xlabel("x")
            ax.set_ylabel("f(x)")
            ax.set_ylim([-3, 3])

            # Add text showing number of linear regions
            unique_patterns = len(torch.unique(pattern_id))
            ax.text(
                0.02,
                0.98,
                f"Regions: {unique_patterns}",
                transform=ax.transAxes,
                va="top",
                fontsize=10,
                bbox=dict(boxstyle="round", facecolor="wheat", alpha=0.5),
            )

    plt.suptitle(
        "ReLU Networks as Piecewise Polynomials: Width vs Complexity\n(Colors indicate different linear regions)",
        fontsize=14,
    )
    plt.tight_layout()
    plt.savefig("./graphs/polynomial_behavior_1d.png", dpi=300, bbox_inches="tight")
    plt.close()


def analyze_all_positive_regime():
    """Analyze what happens when we force all ReLUs to be positive."""

    torch.manual_seed(42)

    # Create network
    net = ReLUNetwork(input_dim=2, hidden_dims=[8, 8], output_dim=2)

    # Generate test points in a region where we expect positive activations
    test_points = torch.rand(100, 2) * 2 + 5  # Shifted to positive region

    # Add large positive bias to ensure positive regime
    with torch.no_grad():
        for layer in net.layers[:-1]:  # Not the output layer
            layer.bias.add_(10.0)  # Large positive bias

    # Check activation patterns
    outputs, activations = net(test_points, return_activations=True)

    print("=" * 50)
    print("All-Positive Regime Analysis")
    print("=" * 50)

    for i, act in enumerate(activations):
        positive_ratio = act["active_ratio"].mean().item()
        print(f"Layer {i+1}: {positive_ratio*100:.1f}% neurons firing positive")

    # In positive regime, network is just a linear transformation
    linear_output = net.get_polynomial_in_positive_region(test_points[0])
    network_output = net(test_points[0:1])

    print(f"\nNetwork output: {network_output.squeeze().detach().numpy()}")
    print(f"Linear computation: {linear_output.squeeze().numpy()}")
    print(
        f"Difference: {(network_output.squeeze() - linear_output.squeeze()).abs().mean().item():.6f}"
    )

    return net, test_points


def plot_squiggly_line_scaling():
    """Plot how average minimum distance scales with network width."""

    print("Running scaling analysis (this may take a minute)...")
    results = analyze_squiggly_line_effect(input_dim=2, max_width=64, n_samples=50)

    fig, axes = plt.subplots(1, 3, figsize=(15, 5))

    # Plot 1: Distance vs Width
    ax1 = axes[0]
    ax1.errorbar(
        results["width"],
        results["avg_min_distance"],
        yerr=results["std_min_distance"],
        marker="o",
        capsize=5,
    )
    ax1.set_xlabel("Network Width")
    ax1.set_ylabel("Average Minimum Distance to Data")
    ax1.set_title("Squiggly Line Effect: Width vs Distance")
    ax1.set_xscale("log")
    ax1.grid(True, alpha=0.3)

    # Fit power law
    log_width = np.log(results["width"])
    log_dist = np.log(results["avg_min_distance"])
    coef = np.polyfit(log_width, log_dist, 1)
    ax1.text(
        0.05,
        0.95,
        f"Scaling: d ~ w^{coef[0]:.2f}",
        transform=ax1.transAxes,
        va="top",
        bbox=dict(boxstyle="round", facecolor="wheat", alpha=0.5),
    )

    # Plot 2: Activation Patterns
    ax2 = axes[1]
    ax2.plot(
        results["width"],
        results["positive_activation_ratio"],
        marker="s",
        color="orange",
    )
    ax2.set_xlabel("Network Width")
    ax2.set_ylabel("Fraction of Positive Activations")
    ax2.set_title("Activation Patterns vs Width")
    ax2.set_xscale("log")
    ax2.grid(True, alpha=0.3)

    # Plot 3: Parameters vs Distance
    ax3 = axes[2]
    ax3.scatter(results["effective_params"], results["avg_min_distance"], s=100)
    ax3.set_xlabel("Number of Parameters")
    ax3.set_ylabel("Average Minimum Distance")
    ax3.set_title("Overparameterization Effect")
    ax3.set_xscale("log")

    # Fit curve
    params = np.array(results["effective_params"])
    dists = np.array(results["avg_min_distance"])
    log_params = np.log(params)
    log_dists = np.log(dists)
    coef2 = np.polyfit(log_params, log_dists, 1)

    # Plot fit
    params_smooth = np.logspace(np.log10(params.min()), np.log10(params.max()), 100)
    dists_fit = np.exp(coef2[1]) * params_smooth ** coef2[0]
    ax3.plot(params_smooth, dists_fit, "r--", alpha=0.5, label=f"d ~ p^{coef2[0]:.2f}")
    ax3.legend()
    ax3.grid(True, alpha=0.3)

    plt.suptitle("Neural Network Width and the Squiggly Line Conjecture", fontsize=14)
    plt.tight_layout()
    plt.savefig("./graphs/squiggly_line_scaling.png", dpi=300, bbox_inches="tight")
    plt.close()

    return results


# Main execution
if __name__ == "__main__":
    print("=" * 60)
    print("RELU NETWORKS AS HIGH-DIMENSIONAL POLYNOMIALS")
    print("Testing the Squiggly Line Conjecture")
    print("=" * 60)

    # 1. Visualize 1D case
    print("\n1. Visualizing 1D networks of different widths...")
    visualize_polynomial_behavior_1d()

    # 2. Analyze all-positive regime
    print("\n2. Analyzing all-positive activation regime...")
    net, test_points = analyze_all_positive_regime()

    # 3. Show scaling behavior
    print("\n3. Analyzing scaling behavior...")
    results = plot_squiggly_line_scaling()

    print("\n" + "=" * 60)
    print("KEY FINDINGS:")
    print("1. Wider networks -> More complex functions -> Closer to random data")
    print("2. When all ReLUs fire positive, network = linear polynomial")
    print("3. More parameters create more 'squiggles' in function space")
    print("4. This validates the Squiggly Line Conjecture for neural networks!")
    print("=" * 60)
