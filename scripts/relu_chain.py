"""
DEFECT WARNING -- read docs/RESOLUTION.md §4 before using any number from here.

Two defects in `analyze_squiggly_line_effect`:

1. input_dim > 1 branch measures ||net(x) - x||, the distance from the network's
   output to its own input. Under Xavier init the output is attenuated as width
   grows, so the metric converges to ||x|| -- the score of the zero function.
   The w^(-alpha), alpha ~ 0.42 "scaling law" is this signal attenuation.

2. input_dim == 1 branch uses point[0] for BOTH coordinates of each data point,
   placing every "random point" on the line y = x.

Metrics deliberately left unfixed as the historical record.
"""
import torch
import torch.nn as nn
import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
import pandas as pd

# Set seaborn style
sns.set_style("whitegrid")
plt.rcParams['figure.figsize'] = (10, 8)


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
    widths = [1, 2, 4, 8, 16, 32]
    x = torch.linspace(-3, 3, 1000).unsqueeze(1)

    # Generate random "data points" to measure distance to
    n_points = 20
    data_x = torch.rand(n_points) * 6 - 3
    data_y = torch.randn(n_points) * 0.5

    # Create data for all widths combined - show complexity vs width using hue
    plt.figure(figsize=(10, 8))
    
    # Collect data for all networks
    all_data = []
    for width in widths:
        net = ReLUNetwork(input_dim=1, hidden_dims=[width, width], output_dim=1)
        
        with torch.no_grad():
            y, activations = net(x, return_activations=True)
            
            # Count unique activation patterns (linear regions)
            activation_pattern = torch.cat(
                [act["post_relu"].mean(dim=1, keepdim=True) > 0 for act in activations],
                dim=1,
            )
            pattern_id = activation_pattern.float() @ (
                2.0 ** torch.arange(len(activations)).float()
            ).unsqueeze(1)
            unique_patterns = len(torch.unique(pattern_id))
            
            # Compute average minimum distance to data points
            min_dists = []
            for i in range(n_points):
                dists = torch.sqrt(
                    (x.squeeze() - data_x[i]) ** 2 + (y.squeeze() - data_y[i]) ** 2
                )
                min_dists.append(dists.min().item())
            avg_dist = np.mean(min_dists)
            
            all_data.append({
                "width": width,
                "regions": unique_patterns,
                "avg_distance": avg_dist,
                "complexity": unique_patterns / width  # Regions per width unit
            })
    
    # Convert to DataFrame for seaborn
    behavior_df = pd.DataFrame(all_data)
    
    # Plot regions vs width
    sns.lineplot(data=behavior_df, x="width", y="regions", marker="o", 
                linewidth=3, markersize=10, color="blue")
    plt.xlabel("Network Width")
    plt.ylabel("Number of Linear Regions")
    plt.title("ReLU Network Complexity: Linear Regions vs Width")
    plt.tight_layout()
    plt.savefig("../graphs/relu_complexity_vs_width.png", dpi=300, bbox_inches="tight")
    plt.close()

    # Plot average distance vs width  
    plt.figure(figsize=(10, 8))
    sns.lineplot(data=behavior_df, x="width", y="avg_distance", marker="o", 
                linewidth=3, markersize=10, color="red")
    plt.xlabel("Network Width")
    plt.ylabel("Average Distance to Data Points")
    plt.title("ReLU Networks: Distance to Random Data vs Width")
    plt.tight_layout()
    plt.savefig("../graphs/relu_distance_vs_width.png", dpi=300, bbox_inches="tight")
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

    # Create DataFrame for consistent plotting
    scaling_data = []
    for i, width in enumerate(results["width"]):
        scaling_data.append({
            "width": width,
            "avg_distance": results["avg_min_distance"][i],
            "std_distance": results["std_min_distance"][i],
            "activation_ratio": results["positive_activation_ratio"][i],
            "effective_params": results["effective_params"][i]
        })
    scaling_df = pd.DataFrame(scaling_data)

    # Plot 1: Distance vs Width with error bars
    plt.figure(figsize=(10, 8))
    plt.errorbar(
        scaling_df["width"],
        scaling_df["avg_distance"],
        yerr=scaling_df["std_distance"],
        marker="o",
        capsize=5,
        linewidth=2,
        markersize=8,
        color='blue'
    )
    plt.xlabel("Network Width")
    plt.ylabel("Average Minimum Distance to Data")
    plt.title("Squiggly Line Effect: Width vs Distance")
    plt.xscale("log")

    # Fit power law
    log_width = np.log(results["width"])
    log_dist = np.log(results["avg_min_distance"])
    coef = np.polyfit(log_width, log_dist, 1)
    plt.text(
        0.05,
        0.95,
        f"Scaling: d ~ w^{coef[0]:.2f}",
        transform=plt.gca().transAxes,
        va="top",
        fontsize=10,
        bbox=dict(boxstyle="round", facecolor="wheat", alpha=0.7),
    )
    plt.tight_layout()
    plt.savefig("../graphs/relu_distance_vs_width_scaling.png", dpi=300, bbox_inches="tight")
    plt.close()

    # Plot 2: Activation Patterns vs Width
    plt.figure(figsize=(10, 8))
    sns.lineplot(
        data=scaling_df,
        x="width",
        y="activation_ratio",
        marker="s",
        color="orange",
        linewidth=2,
        markersize=8
    )
    plt.xlabel("Network Width")
    plt.ylabel("Fraction of Positive Activations")
    plt.title("Activation Patterns vs Width")
    plt.xscale("log")
    plt.tight_layout()
    plt.savefig("../graphs/relu_activation_patterns_vs_width.png", dpi=300, bbox_inches="tight")
    plt.close()

    # Plot 3: Parameters vs Distance with fit curve
    plt.figure(figsize=(10, 8))
    plt.scatter(scaling_df["effective_params"], scaling_df["avg_distance"], s=100, color='green', alpha=0.7)
    plt.xlabel("Number of Parameters")
    plt.ylabel("Average Minimum Distance")
    plt.title("Overparameterization Effect")
    plt.xscale("log")

    # Fit curve
    params = np.array(results["effective_params"])
    dists = np.array(results["avg_min_distance"])
    log_params = np.log(params)
    log_dists = np.log(dists)
    coef2 = np.polyfit(log_params, log_dists, 1)

    # Plot fit
    params_smooth = np.logspace(np.log10(params.min()), np.log10(params.max()), 100)
    dists_fit = np.exp(coef2[1]) * params_smooth ** coef2[0]
    plt.plot(params_smooth, dists_fit, "r--", alpha=0.7, linewidth=2, label=f"d ~ p^{coef2[0]:.2f}")
    plt.legend()
    plt.tight_layout()
    plt.savefig("../graphs/relu_overparameterization_effect.png", dpi=300, bbox_inches="tight")
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
    print("Individual graphs saved to ./graphs/:")
    print("- relu_complexity_vs_width.png")
    print("- relu_distance_vs_width.png")
    print("- relu_distance_vs_width_scaling.png")
    print("- relu_activation_patterns_vs_width.png")
    print("- relu_overparameterization_effect.png")
    print("=" * 60)
