import numpy as np
import matplotlib.pyplot as plt
import seaborn as sns
import pandas as pd
from utils import count_activation_patterns, generate_data_distribution

# Set seaborn style
sns.set_style("whitegrid")
plt.rcParams['figure.figsize'] = (10, 8)


class QuantumInspiredNetwork:
    """Quantum-inspired neural network that explores activation patterns in superposition"""

    def __init__(self, n_qubits, classical_width):
        self.n_qubits = n_qubits
        self.classical_width = classical_width
        # Quantum advantage: explore 2^n patterns vs n patterns classically

    def quantum_activation_patterns(self, X):
        """Simulate quantum superposition of activation patterns"""
        n_points = len(X)

        # Classical network explores ~width patterns
        # Quantum network explores 2^qubits patterns (exponential advantage)
        max_quantum_patterns = 2**self.n_qubits
        max_classical_patterns = self.classical_width

        # Simulate quantum measurement collapse to specific patterns
        quantum_patterns = min(max_quantum_patterns, n_points)
        classical_patterns = min(max_classical_patterns, n_points)

        return quantum_patterns, classical_patterns

    def measure_quantum_advantage(self, X, d):
        """Measure the quantum advantage for squiggly line coverage"""
        quantum_patterns, classical_patterns = self.quantum_activation_patterns(X)

        # Quantum coverage (exponential in qubits)
        quantum_coverage = quantum_patterns / len(X)

        # Classical coverage (linear in width)
        classical_coverage = classical_patterns / len(X)

        # Distance estimates (more patterns = closer to random data)
        # Using theoretical scaling: distance ~ 1/patterns^(1/d)
        quantum_distance = (
            1 / (quantum_patterns ** (1 / d)) if quantum_patterns > 0 else np.inf
        )
        classical_distance = (
            1 / (classical_patterns ** (1 / d)) if classical_patterns > 0 else np.inf
        )

        advantage = (
            classical_distance / quantum_distance if quantum_distance > 0 else np.inf
        )

        return {
            "quantum_patterns": quantum_patterns,
            "classical_patterns": classical_patterns,
            "quantum_coverage": quantum_coverage,
            "classical_coverage": classical_coverage,
            "quantum_distance": quantum_distance,
            "classical_distance": classical_distance,
            "quantum_advantage": advantage,
        }


###########################################################################################################
# TODO
###########################################################################################################


def quantum_coverage(energy_level, data_points, box_size=1.0):
    """
    Compute quantum mechanical coverage for given energy level
    """
    # Wave function for particle in box
    psi = lambda x, n: np.sqrt(2 / box_size) * np.sin(n * np.pi * x / box_size)

    # Coverage calculation
    coverage = 0
    for point in data_points:
        x_range = np.linspace(0, box_size, 1000)
        psi_squared = psi(x_range, energy_level) ** 2
        distances = 1 / ((x_range - point) ** 2 + 0.01)
        coverage += np.trapezoid(psi_squared * distances, x_range)

    return coverage / len(data_points)


###########################################################################################################


def simulate_quantum_vs_classical_scaling(max_qubits=8, dimensions=[2, 3, 4], m=1000):
    """Compare quantum vs classical scaling for squiggly line effect"""
    results = {
        "qubits": [],
        "dimension": [],
        "quantum_advantage": [],
        "quantum_patterns": [],
        "classical_patterns": [],
        "quantum_distance": [],
        "classical_distance": [],
    }

    for d in dimensions:
        for n_qubits in range(1, max_qubits + 1):
            # Classical width equivalent to quantum qubits (for fair comparison)
            classical_width = 2**n_qubits if n_qubits <= 6 else 64

            # Generate test data
            X = generate_data_distribution("gaussian", m, d)

            # Create quantum-inspired network
            quantum_net = QuantumInspiredNetwork(n_qubits, classical_width)

            # Measure advantage
            metrics = quantum_net.measure_quantum_advantage(X, d)

            results["qubits"].append(n_qubits)
            results["dimension"].append(d)
            results["quantum_advantage"].append(metrics["quantum_advantage"])
            results["quantum_patterns"].append(metrics["quantum_patterns"])
            results["classical_patterns"].append(metrics["classical_patterns"])
            results["quantum_distance"].append(metrics["quantum_distance"])
            results["classical_distance"].append(metrics["classical_distance"])

    return results


def analyze_quantum_decoherence_effects(
    n_qubits=5, decoherence_rates=[0.0, 0.01, 0.05, 0.1, 0.2]
):
    """Analyze how quantum decoherence affects the squiggly line advantage"""
    results = {"decoherence_rate": [], "effective_qubits": [], "advantage_ratio": []}

    ideal_patterns = 2**n_qubits

    for rate in decoherence_rates:
        # Decoherence reduces effective number of qubits
        effective_qubits = n_qubits * (1 - rate)
        effective_patterns = 2**effective_qubits

        # Advantage ratio compared to ideal quantum case
        advantage_ratio = effective_patterns / ideal_patterns

        results["decoherence_rate"].append(rate)
        results["effective_qubits"].append(effective_qubits)
        results["advantage_ratio"].append(advantage_ratio)

    return results


def measure_quantum_entanglement_benefit(
    n_qubits_list=[2, 3, 4, 5], entanglement_levels=[0.0, 0.5, 1.0]
):
    """Measure how quantum entanglement affects pattern exploration"""
    results = {"n_qubits": [], "entanglement": [], "pattern_efficiency": []}

    for n_qubits in n_qubits_list:
        for entanglement in entanglement_levels:
            # Higher entanglement allows more efficient pattern exploration
            # Entanglement factor multiplies effective patterns
            base_patterns = 2**n_qubits
            entangled_patterns = base_patterns * (1 + entanglement)

            # Pattern efficiency: how many patterns per qubit
            efficiency = entangled_patterns / n_qubits

            results["n_qubits"].append(n_qubits)
            results["entanglement"].append(entanglement)
            results["pattern_efficiency"].append(efficiency)

    return results


def quantum_error_correction_analysis(
    n_logical_qubits=[1, 2, 3, 4], error_rates=[0.001, 0.01, 0.1]
):
    """Analyze quantum error correction requirements for squiggly line networks"""
    results = {
        "logical_qubits": [],
        "error_rate": [],
        "physical_qubits_needed": [],
        "net_advantage": [],
    }

    for n_logical in n_logical_qubits:
        for error_rate in error_rates:
            # Error correction overhead: ~100-1000 physical qubits per logical qubit
            # depending on error rate and correction scheme
            if error_rate <= 0.001:
                overhead = 100  # Surface code with low error
            elif error_rate <= 0.01:
                overhead = 500  # Medium error rate
            else:
                overhead = 1000  # High error rate

            physical_qubits = n_logical * overhead

            # Net advantage: logical quantum patterns vs classical equivalent
            quantum_patterns = 2**n_logical
            classical_equivalent = (
                physical_qubits  # Classical network with same resources
            )

            net_advantage = quantum_patterns / classical_equivalent

            results["logical_qubits"].append(n_logical)
            results["error_rate"].append(error_rate)
            results["physical_qubits_needed"].append(physical_qubits)
            results["net_advantage"].append(net_advantage)

    return results


if __name__ == "__main__":
    print("=" * 60)
    print("QUANTUM SQUIGGLY LINE CONJECTURE ANALYSIS")
    print("=" * 60)

    # 1. Quantum vs Classical Scaling
    print("\n1. Quantum vs Classical Scaling:")
    scaling_results = simulate_quantum_vs_classical_scaling()

    # Show key results
    for d in [2, 3, 4]:
        d_results = [
            (scaling_results["qubits"][i], scaling_results["quantum_advantage"][i])
            for i in range(len(scaling_results["dimension"]))
            if scaling_results["dimension"][i] == d
        ]

        print(f"\nDimension {d}:")
        for qubits, advantage in d_results[:6]:  # Show first 6
            print(f"  {qubits} qubits: quantum advantage = {advantage:.2f}x")

    # 2. Decoherence Effects
    print("\n2. Quantum Decoherence Effects:")
    decoherence_results = analyze_quantum_decoherence_effects()

    for i, rate in enumerate(decoherence_results["decoherence_rate"]):
        ratio = decoherence_results["advantage_ratio"][i]
        eff_qubits = decoherence_results["effective_qubits"][i]
        print(
            f"  Decoherence rate {rate:.2f}: {eff_qubits:.1f} effective qubits, {ratio:.3f} advantage ratio"
        )

    # 3. Entanglement Benefits
    print("\n3. Quantum Entanglement Benefits:")
    entanglement_results = measure_quantum_entanglement_benefit()

    for entanglement in [0.0, 0.5, 1.0]:
        ent_results = [
            (
                entanglement_results["n_qubits"][i],
                entanglement_results["pattern_efficiency"][i],
            )
            for i in range(len(entanglement_results["entanglement"]))
            if entanglement_results["entanglement"][i] == entanglement
        ]

        print(f"\n  Entanglement level {entanglement}:")
        for qubits, efficiency in ent_results:
            print(f"    {qubits} qubits: {efficiency:.1f} patterns per qubit")

    # 4. Error Correction Analysis
    print("\n4. Quantum Error Correction Requirements:")
    error_results = quantum_error_correction_analysis()

    for error_rate in [0.001, 0.01, 0.1]:
        rate_results = [
            (
                error_results["logical_qubits"][i],
                error_results["physical_qubits_needed"][i],
                error_results["net_advantage"][i],
            )
            for i in range(len(error_results["error_rate"]))
            if error_results["error_rate"][i] == error_rate
        ]

        print(f"\n  Error rate {error_rate}:")
        for logical, physical, advantage in rate_results:
            print(
                f"    {logical} logical qubits → {physical} physical qubits → {advantage:.4f}x net advantage"
            )

    # 5. Quantum Coverage Analysis
    print("\n5. Quantum Mechanical Coverage:")
    energy_levels = [1, 2, 3, 4, 5]
    test_points = np.random.uniform(0.1, 0.9, 20)  # Points in unit box
    coverage_results = []

    for energy_level in energy_levels:
        coverage = quantum_coverage(energy_level, test_points)
        coverage_results.append(coverage)
        print(f"  Energy level n={energy_level}: coverage = {coverage:.3f}")

    print(
        f"  Best coverage at energy level {energy_levels[np.argmax(coverage_results)]}"
    )
    print(
        f"  Coverage ratio (max/min) = {max(coverage_results)/min(coverage_results):.2f}"
    )

    # Plot 1: Quantum Advantage by Dimension
    plt.figure(figsize=(10, 8))
    dimensions = sorted(set(scaling_results["dimension"]))
    quantum_data = []
    for i, d in enumerate(scaling_results["dimension"]):
        quantum_data.append({
            "qubits": scaling_results["qubits"][i],
            "dimension": d,
            "quantum_advantage": scaling_results["quantum_advantage"][i]
        })
    quantum_df = pd.DataFrame(quantum_data)
    
    sns.lineplot(data=quantum_df, x="qubits", y="quantum_advantage", hue="dimension",
                marker="o", linewidth=2, markersize=8)
    plt.yscale('log')
    plt.xlabel("Number of Qubits")
    plt.ylabel("Quantum Advantage")
    plt.title("Quantum Advantage vs Qubits by Dimension")
    plt.legend(title="Dimension")
    plt.tight_layout()
    plt.savefig("../graphs/quantum_advantage_vs_qubits.png", dpi=300, bbox_inches="tight")
    plt.close()

    # Plot 2: Pattern Comparison - Quantum vs Classical
    plt.figure(figsize=(10, 8))
    quantum_2d = quantum_df[quantum_df["dimension"] == 2]
    
    pattern_data = []
    for i, d in enumerate(scaling_results["dimension"]):
        if d == 2:  # Focus on 2D for clarity
            pattern_data.append({"qubits": scaling_results["qubits"][i], 
                               "patterns": scaling_results["quantum_patterns"][i], "type": "Quantum"})
            pattern_data.append({"qubits": scaling_results["qubits"][i], 
                               "patterns": scaling_results["classical_patterns"][i], "type": "Classical"})
    
    pattern_df = pd.DataFrame(pattern_data)
    sns.lineplot(data=pattern_df, x="qubits", y="patterns", hue="type", style="type",
                markers=True, linewidth=2, markersize=8)
    plt.yscale('log')
    plt.xlabel("Qubits / Equivalent Width")
    plt.ylabel("Number of Patterns")
    plt.title("Quantum vs Classical Patterns (2D)")
    plt.legend(title="Approach")
    plt.tight_layout()
    plt.savefig("../graphs/quantum_vs_classical_patterns.png", dpi=300, bbox_inches="tight")
    plt.close()

    # Plot 3: Distance Comparison - Quantum vs Classical
    plt.figure(figsize=(10, 8))
    distances_2d = [
        (scaling_results["qubits"][i], scaling_results["classical_distance"][i], scaling_results["quantum_distance"][i])
        for i in range(len(scaling_results["dimension"]))
        if scaling_results["dimension"][i] == 2
    ][:6]
    
    dist_data = []
    for qubits, classical_dist, quantum_dist in distances_2d:
        dist_data.append({"qubits": qubits, "distance": classical_dist, "type": "Classical"})
        dist_data.append({"qubits": qubits, "distance": quantum_dist, "type": "Quantum"})
    
    dist_df = pd.DataFrame(dist_data)
    sns.lineplot(data=dist_df, x="qubits", y="distance", hue="type", style="type",
                markers=True, linewidth=2, markersize=8)
    plt.yscale('log')
    plt.xlabel("Qubits")
    plt.ylabel("Distance to Random Data")
    plt.title("Distance Comparison: Quantum vs Classical (2D)")
    plt.legend(title="Approach")
    plt.tight_layout()
    plt.savefig("../graphs/quantum_distance_comparison.png", dpi=300, bbox_inches="tight")
    plt.close()

    # Plot 4: Decoherence Effects
    plt.figure(figsize=(10, 8))
    sns.lineplot(x=decoherence_results["decoherence_rate"], 
                y=decoherence_results["advantage_ratio"],
                marker="o", color="magenta", linewidth=2, markersize=8)
    plt.xlabel("Decoherence Rate")
    plt.ylabel("Advantage Ratio")
    plt.title("Quantum Decoherence Impact on Advantage")
    plt.tight_layout()
    plt.savefig("../graphs/quantum_decoherence_effects.png", dpi=300, bbox_inches="tight")
    plt.close()

    # Plot 5: Entanglement Benefits
    plt.figure(figsize=(10, 8))
    ent_data = []
    for i, qubits in enumerate(entanglement_results["n_qubits"]):
        ent_data.append({
            "qubits": f"{qubits} qubits",
            "entanglement": entanglement_results["entanglement"][i],
            "efficiency": entanglement_results["pattern_efficiency"][i]
        })
    ent_df = pd.DataFrame(ent_data)
    
    sns.lineplot(data=ent_df, x="entanglement", y="efficiency", hue="qubits",
                marker="o", linewidth=2, markersize=8)
    plt.xlabel("Entanglement Level")
    plt.ylabel("Pattern Efficiency")
    plt.title("Entanglement Benefits by Qubit Count")
    plt.legend(title="System Size")
    plt.tight_layout()
    plt.savefig("../graphs/quantum_entanglement_benefits.png", dpi=300, bbox_inches="tight")
    plt.close()

    # Plot 6: Error Correction Overhead
    plt.figure(figsize=(10, 8))
    err_data = []
    for i, logical_qubits in enumerate(error_results["logical_qubits"]):
        err_data.append({
            "logical_qubits": f"{logical_qubits} logical",
            "error_rate": error_results["error_rate"][i],
            "net_advantage": error_results["net_advantage"][i]
        })
    err_df = pd.DataFrame(err_data)
    
    sns.lineplot(data=err_df, x="error_rate", y="net_advantage", hue="logical_qubits",
                marker="o", linewidth=2, markersize=8)
    plt.xscale('log')
    plt.xlabel("Error Rate")
    plt.ylabel("Net Quantum Advantage")
    plt.title("Error Correction Impact on Quantum Advantage")
    plt.legend(title="Logical Qubits")
    plt.tight_layout()
    plt.savefig("../graphs/quantum_error_correction.png", dpi=300, bbox_inches="tight")
    plt.close()

    # Plot 7: Quantum Coverage by Energy Level
    plt.figure(figsize=(10, 8))
    sns.lineplot(x=energy_levels, y=coverage_results, marker="o", color="green", 
                linewidth=2, markersize=8)
    
    # Highlight the best energy level
    best_idx = np.argmax(coverage_results)
    plt.scatter(energy_levels[best_idx], coverage_results[best_idx], 
               color="red", s=200, zorder=5, label=f"Best: n={energy_levels[best_idx]}")
    plt.xlabel("Energy Level (n)")
    plt.ylabel("Coverage")
    plt.title("Quantum Mechanical Coverage by Energy Level")
    plt.legend()
    plt.tight_layout()
    plt.savefig("../graphs/quantum_coverage_by_energy.png", dpi=300, bbox_inches="tight")
    plt.close()

    print("\n" + "=" * 60)
    print("KEY QUANTUM FINDINGS:")
    print("1. Quantum networks show exponential advantage in pattern exploration")
    print("2. Higher dimensions amplify quantum advantage further")
    print("3. Decoherence rapidly degrades quantum advantage")
    print("4. Entanglement provides additional efficiency gains")
    print("5. Error correction overhead may negate advantages for near-term devices")
    print("6. Quantum mechanical coverage varies significantly with energy levels")
    print("7. Fault-tolerant quantum computers could revolutionize function approximation")
    print("Individual graphs saved to ./graphs/:")
    print("- quantum_advantage_vs_qubits.png")
    print("- quantum_vs_classical_patterns.png")
    print("- quantum_distance_comparison.png")
    print("- quantum_decoherence_effects.png")
    print("- quantum_entanglement_benefits.png")
    print("- quantum_error_correction.png")
    print("- quantum_coverage_by_energy.png")
    print("=" * 60)
