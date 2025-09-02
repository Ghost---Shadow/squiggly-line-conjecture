import torch
import torch.nn as nn
import torch.optim as optim
import numpy as np
import matplotlib.pyplot as plt
from sklearn.decomposition import PCA
import os

# Disable interactive plotting
plt.ioff()

# Set random seeds
torch.manual_seed(42)
np.random.seed(42)

# Create output directory
os.makedirs("graphs", exist_ok=True)


class SimpleRNN(nn.Module):
    def __init__(self, vocab_size, embedding_dim=16, hidden_dim=32):
        super(SimpleRNN, self).__init__()
        self.vocab_size = vocab_size
        self.embedding_dim = embedding_dim
        self.hidden_dim = hidden_dim

        # Token embedding layer
        self.embedding = nn.Embedding(vocab_size, embedding_dim)

        # Simple RNN
        self.rnn = nn.RNN(embedding_dim, hidden_dim, batch_first=True)

        # Output projection
        self.output_projection = nn.Linear(hidden_dim, vocab_size)

        # Store trajectories
        self.embedding_trajectory = None
        self.hidden_trajectory = None

    def forward(self, x):
        batch_size, seq_len = x.size()

        # Get embeddings
        embeddings = self.embedding(x)
        self.embedding_trajectory = embeddings.detach().cpu().numpy()[0]  # First batch

        # RNN processing
        rnn_out, _ = self.rnn(embeddings)
        self.hidden_trajectory = rnn_out.detach().cpu().numpy()[0]  # First batch

        # Output logits
        logits = self.output_projection(rnn_out)

        return logits


def create_simple_sentence():
    """Create simple 5-token vocabulary and basic sentence"""

    # Very simple vocabulary: 5 tokens only
    vocab = ["cat", "dog", "runs", "jumps", "sits"]
    vocab_size = len(vocab)

    # Token mappings
    token_to_idx = {token: idx for idx, token in enumerate(vocab)}
    idx_to_token = {idx: token for token, idx in token_to_idx.items()}

    # Create a simple sentence pattern that repeats
    sentence_pattern = [
        "cat",
        "runs",
        "dog",
        "jumps",
        "cat",
        "sits",
        "dog",
        "runs",
        "cat",
        "jumps",
    ]

    # Convert to indices
    sentence_indices = [token_to_idx[token] for token in sentence_pattern]

    return (
        torch.LongTensor([sentence_indices]),
        token_to_idx,
        idx_to_token,
        sentence_pattern,
    )


def train_simple_model(model, data, epochs=200):
    """Train on the simple sentence"""
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    model.to(device)
    data = data.to(device)

    criterion = nn.CrossEntropyLoss()
    optimizer = optim.Adam(model.parameters(), lr=0.01)

    print("Training simple RNN on basic sentence...")
    for epoch in range(epochs):
        model.train()

        inputs = data[:, :-1]  # All except last token
        targets = data[:, 1:]  # All except first token

        optimizer.zero_grad()
        logits = model(inputs)

        loss = criterion(logits.reshape(-1, model.vocab_size), targets.reshape(-1))
        loss.backward()
        optimizer.step()

        if epoch % 40 == 0:
            print(f"Epoch {epoch}/{epochs}, Loss: {loss.item():.4f}")

    print("Training completed!")
    return model


def visualize_wind_vocab_trajectory(model, data, idx_to_token, sentence_pattern):
    """Visualize trajectory with x=wind (time/position) and y=vocab tokens"""
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    model.eval()

    sequence = data[0].to(device)

    with torch.no_grad():
        # Forward pass
        logits = model(sequence.unsqueeze(0))

        # Get trajectories
        embeddings = model.embedding_trajectory  # Shape: (seq_len, embedding_dim)
        hidden_states = model.hidden_trajectory  # Shape: (seq_len, hidden_dim)

    seq_len = len(sentence_pattern)

    # Create figure with wind (x) vs vocab (y) perspective
    fig, axes = plt.subplots(2, 3, figsize=(18, 12))
    fig.suptitle(
        "🌪️ Wind Lanes (X) vs Vocabulary Tokens (Y): Squiggly Language Trajectory",
        fontsize=16,
    )

    # 1. Main plot: Wind position (x) vs Token ID (y)
    wind_positions = range(seq_len)  # Time/position along sequence = "wind"
    token_ids = [sequence[i].item() for i in range(seq_len)]

    axes[0, 0].plot(
        wind_positions,
        token_ids,
        "o-",
        linewidth=4,
        markersize=10,
        color="red",
        alpha=0.8,
        label="Token Trajectory",
    )

    # Add token labels
    for i, (wind_pos, token_id) in enumerate(zip(wind_positions, token_ids)):
        axes[0, 0].annotate(
            f"{sentence_pattern[i]}",
            (wind_pos, token_id),
            xytext=(0, 15),
            textcoords="offset points",
            ha="center",
            va="bottom",
            fontsize=10,
            bbox=dict(boxstyle="round,pad=0.3", facecolor="yellow", alpha=0.8),
        )

    axes[0, 0].set_title(
        "Wind Position vs Vocabulary Token 🌪️📝\n(The main squiggly trajectory)"
    )
    axes[0, 0].set_xlabel("Wind Position (Token Sequence Position)")
    axes[0, 0].set_ylabel("Vocabulary Token ID")
    axes[0, 0].set_yticks(range(len(idx_to_token)))
    axes[0, 0].set_yticklabels([idx_to_token[i] for i in range(len(idx_to_token))])
    axes[0, 0].grid(True, alpha=0.3)
    axes[0, 0].legend()

    # 2. Hidden state "wind strength" analysis
    # Project hidden states to 1D to represent "wind strength"
    pca_hidden_1d = PCA(n_components=1)
    wind_strength = pca_hidden_1d.fit_transform(hidden_states).flatten()

    axes[0, 1].plot(
        wind_positions,
        wind_strength,
        "s-",
        linewidth=3,
        markersize=8,
        color="blue",
        alpha=0.8,
        label="Wind Strength",
    )
    axes[0, 1].fill_between(wind_positions, wind_strength, alpha=0.3, color="blue")

    # Mark strong wind points
    strong_wind_threshold = np.percentile(np.abs(wind_strength), 80)
    strong_winds = [
        i for i, w in enumerate(wind_strength) if abs(w) > strong_wind_threshold
    ]

    for wind_point in strong_winds:
        axes[0, 1].axvline(x=wind_point, color="orange", alpha=0.7, linestyle="--")
        axes[0, 1].text(
            wind_point,
            wind_strength[wind_point],
            sentence_pattern[wind_point],
            rotation=90,
            fontsize=8,
            ha="right",
            va="bottom",
        )

    axes[0, 1].set_title("Hidden State Wind Strength 💨\n(RNN internal dynamics)")
    axes[0, 1].set_xlabel("Wind Position")
    axes[0, 1].set_ylabel("Wind Strength (Hidden State PC1)")
    axes[0, 1].grid(True, alpha=0.3)
    axes[0, 1].legend()

    # 3. Embedding "altitude" changes
    # Project embeddings to 1D to represent "altitude" in embedding space
    pca_emb_1d = PCA(n_components=1)
    embedding_altitude = pca_emb_1d.fit_transform(embeddings).flatten()

    axes[0, 2].plot(
        wind_positions,
        embedding_altitude,
        "^-",
        linewidth=3,
        markersize=8,
        color="green",
        alpha=0.8,
        label="Embedding Altitude",
    )
    axes[0, 2].fill_between(
        wind_positions, embedding_altitude, alpha=0.3, color="green"
    )

    axes[0, 2].set_title(
        "Embedding Altitude Changes 🏔️\n(Movement through semantic space)"
    )
    axes[0, 2].set_xlabel("Wind Position")
    axes[0, 2].set_ylabel("Embedding Altitude (PC1)")
    axes[0, 2].grid(True, alpha=0.3)
    axes[0, 2].legend()

    # 4. Token transition jumps (vocab changes)
    transition_jumps = []
    transition_labels = []

    for i in range(len(token_ids) - 1):
        jump_size = abs(token_ids[i + 1] - token_ids[i])
        transition_jumps.append(jump_size)
        transition_labels.append(f"{sentence_pattern[i]}→{sentence_pattern[i+1]}")

    transition_positions = range(len(transition_jumps))
    axes[1, 0].bar(
        transition_positions,
        transition_jumps,
        color="purple",
        alpha=0.7,
        edgecolor="black",
    )

    # Label transitions
    for i, (pos, jump, label) in enumerate(
        zip(transition_positions, transition_jumps, transition_labels)
    ):
        axes[1, 0].text(
            pos, jump + 0.1, label, rotation=45, fontsize=8, ha="left", va="bottom"
        )

    axes[1, 0].set_title(
        "Vocabulary Jump Sizes 🦘\n(How far model jumps between tokens)"
    )
    axes[1, 0].set_xlabel("Transition Position")
    axes[1, 0].set_ylabel("Vocabulary Distance")
    axes[1, 0].grid(True, alpha=0.3)

    # 5. Combined wind-vocab trajectory with vectors
    # Show the trajectory as vectors in wind-vocab space
    axes[1, 1].plot(
        wind_positions,
        token_ids,
        "o-",
        linewidth=4,
        markersize=12,
        color="red",
        alpha=0.8,
    )

    # Add velocity vectors
    for i in range(len(wind_positions) - 1):
        dx = 1  # Always move forward in wind (time)
        dy = token_ids[i + 1] - token_ids[i]  # Change in vocabulary

        # Color code by jump magnitude
        jump_color = "green" if abs(dy) <= 1 else "orange" if abs(dy) <= 2 else "red"

        axes[1, 1].arrow(
            wind_positions[i],
            token_ids[i],
            dx * 0.8,
            dy * 0.8,
            head_width=0.1,
            head_length=0.1,
            fc=jump_color,
            ec=jump_color,
            alpha=0.7,
            linewidth=2,
        )

    # Add token labels
    for wind_pos, token_id, token in zip(wind_positions, token_ids, sentence_pattern):
        axes[1, 1].annotate(
            token,
            (wind_pos, token_id),
            xytext=(0, 20),
            textcoords="offset points",
            ha="center",
            va="bottom",
            fontsize=12,
            fontweight="bold",
            bbox=dict(boxstyle="round,pad=0.4", facecolor="yellow", alpha=0.8),
        )

    axes[1, 1].set_title(
        "Wind-Vocab Trajectory with Velocity Vectors ➡️\n(Green=small jump, Orange=medium, Red=large)"
    )
    axes[1, 1].set_xlabel("Wind Position (Sequence Time)")
    axes[1, 1].set_ylabel("Vocabulary Token ID")
    axes[1, 1].set_yticks(range(len(idx_to_token)))
    axes[1, 1].set_yticklabels([idx_to_token[i] for i in range(len(idx_to_token))])
    axes[1, 1].grid(True, alpha=0.3)

    # 6. Squiggliness heatmap: Show trajectory density
    # Create 2D histogram of wind position vs vocab token
    wind_bins = np.linspace(-0.5, len(wind_positions) - 0.5, len(wind_positions) + 1)
    vocab_bins = np.linspace(-0.5, len(idx_to_token) - 0.5, len(idx_to_token) + 1)

    # Create trajectory heatmap
    trajectory_heatmap = np.zeros((len(idx_to_token), len(wind_positions)))

    for wind_pos, token_id in zip(wind_positions, token_ids):
        if 0 <= token_id < len(idx_to_token) and 0 <= wind_pos < len(wind_positions):
            trajectory_heatmap[token_id, wind_pos] = 1

    # Add "squiggle effect" by showing transition probabilities
    for i in range(len(wind_positions) - 1):
        current_token = token_ids[i]
        next_token = token_ids[i + 1]
        # Add transition intensity
        if 0 <= current_token < len(idx_to_token):
            trajectory_heatmap[current_token, i] += 0.5
        if 0 <= next_token < len(idx_to_token):
            trajectory_heatmap[next_token, i + 1] += 0.5

    im = axes[1, 2].imshow(
        trajectory_heatmap,
        cmap="hot",
        aspect="auto",
        extent=[0, len(wind_positions) - 1, 0, len(idx_to_token) - 1],
        origin="lower",
        alpha=0.8,
    )

    # Overlay the actual trajectory
    axes[1, 2].plot(
        wind_positions, token_ids, "w-", linewidth=4, alpha=0.9, label="Trajectory"
    )
    axes[1, 2].scatter(
        wind_positions,
        token_ids,
        c="white",
        s=100,
        edgecolor="black",
        linewidth=2,
        zorder=10,
    )

    axes[1, 2].set_title("Trajectory Heatmap 🔥\n(Wind × Vocab density map)")
    axes[1, 2].set_xlabel("Wind Position")
    axes[1, 2].set_ylabel("Vocabulary Token ID")
    axes[1, 2].set_yticks(range(len(idx_to_token)))
    axes[1, 2].set_yticklabels([idx_to_token[i] for i in range(len(idx_to_token))])
    plt.colorbar(im, ax=axes[1, 2])
    axes[1, 2].legend()

    plt.tight_layout()
    plt.savefig(
        "graphs/wind_vocab_trajectory.png",
        dpi=300,
        bbox_inches="tight",
    )
    plt.close()

    return wind_positions, token_ids, sentence_pattern


def analyze_squiggliness_metrics(
    wind_positions, token_ids, sentence_pattern, embeddings, hidden_states, idx_to_token
):
    """Analyze the squiggliness of the wind-vocab trajectory"""

    fig, axes = plt.subplots(2, 2, figsize=(16, 12))
    fig.suptitle("🐍 Squiggliness Analysis: Wind Lane Complexity Metrics", fontsize=16)

    # 1. Vocabulary jump analysis
    vocab_jumps = []
    for i in range(len(token_ids) - 1):
        jump = abs(token_ids[i + 1] - token_ids[i])
        vocab_jumps.append(jump)

    axes[0, 0].bar(
        range(len(vocab_jumps)),
        vocab_jumps,
        color=[
            "green" if j <= 1 else "orange" if j <= 2 else "red" for j in vocab_jumps
        ],
        alpha=0.7,
        edgecolor="black",
    )

    # Label each transition
    for i, (jump, pattern) in enumerate(zip(vocab_jumps, sentence_pattern[:-1])):
        next_token = sentence_pattern[i + 1]
        axes[0, 0].text(
            i,
            jump + 0.1,
            f"{pattern}→{next_token}",
            rotation=45,
            fontsize=9,
            ha="left",
            va="bottom",
        )

    axes[0, 0].set_title(
        "Vocabulary Jump Distances 🦘\n(Green=small, Orange=medium, Red=large)"
    )
    axes[0, 0].set_xlabel("Transition Position")
    axes[0, 0].set_ylabel("Vocabulary Distance")
    axes[0, 0].grid(True, alpha=0.3)

    # 2. Embedding space movement (2D projection)
    pca_emb = PCA(n_components=2)
    embeddings_2d = pca_emb.fit_transform(embeddings)

    # Plot the embedding trajectory
    axes[0, 1].plot(
        embeddings_2d[:, 0],
        embeddings_2d[:, 1],
        "o-",
        linewidth=3,
        markersize=8,
        color="purple",
        alpha=0.8,
    )

    # Add token labels at each point
    for i, (point, token) in enumerate(zip(embeddings_2d, sentence_pattern)):
        axes[0, 1].annotate(
            f"{i}:{token}",
            point,
            xytext=(5, 5),
            textcoords="offset points",
            fontsize=8,
            ha="left",
            va="bottom",
            bbox=dict(boxstyle="round,pad=0.3", facecolor="lightblue", alpha=0.7),
        )

    axes[0, 1].set_title(
        "Embedding Space Squiggle 🌀\n(2D projection of semantic trajectory)"
    )
    axes[0, 1].set_xlabel("Embedding PC1")
    axes[0, 1].set_ylabel("Embedding PC2")
    axes[0, 1].grid(True, alpha=0.3)

    # 3. Wind strength vs vocabulary choice
    # Use hidden state magnitude as "wind strength"
    wind_strengths = np.linalg.norm(hidden_states, axis=1)

    # Create scatter plot: wind strength (x) vs token choice (y)
    axes[1, 0].scatter(
        wind_strengths,
        token_ids,
        c=range(len(token_ids)),
        cmap="viridis",
        s=100,
        alpha=0.8,
        edgecolor="black",
        linewidth=1,
    )

    # Connect the points to show trajectory
    axes[1, 0].plot(wind_strengths, token_ids, "-", linewidth=2, color="red", alpha=0.6)

    # Label points
    for i, (strength, token_id, token) in enumerate(
        zip(wind_strengths, token_ids, sentence_pattern)
    ):
        axes[1, 0].annotate(
            f"{i}:{token}",
            (strength, token_id),
            xytext=(3, 3),
            textcoords="offset points",
            fontsize=8,
            ha="left",
            va="bottom",
        )

    axes[1, 0].set_title(
        "Wind Strength vs Token Choice 💨\n(Hidden state magnitude vs vocabulary)"
    )
    axes[1, 0].set_xlabel("Wind Strength (Hidden State Magnitude)")
    axes[1, 0].set_ylabel("Vocabulary Token ID")
    axes[1, 0].set_yticks(range(len(idx_to_token)))
    axes[1, 0].set_yticklabels([idx_to_token[i] for i in range(len(idx_to_token))])
    axes[1, 0].grid(True, alpha=0.3)

    # 4. Trajectory complexity analysis
    # Calculate total "squiggliness" using multiple metrics

    # Metric 1: Total vocabulary distance traveled
    total_vocab_distance = sum(vocab_jumps)

    # Metric 2: Embedding path length
    embedding_path_length = sum(
        np.linalg.norm(embeddings_2d[i + 1] - embeddings_2d[i])
        for i in range(len(embeddings_2d) - 1)
    )

    # Metric 3: Hidden state path length
    hidden_path_length = sum(
        np.linalg.norm(hidden_states[i + 1] - hidden_states[i])
        for i in range(len(hidden_states) - 1)
    )

    # Metric 4: Number of direction changes
    direction_changes = sum(
        1
        for i in range(len(vocab_jumps) - 1)
        if (token_ids[i + 1] - token_ids[i]) * (token_ids[i + 2] - token_ids[i + 1]) < 0
    )

    metrics = [
        "Total Vocab\nDistance",
        "Embedding\nPath Length",
        "Hidden State\nPath Length",
        "Direction\nChanges",
    ]
    values = [
        total_vocab_distance,
        embedding_path_length,
        hidden_path_length,
        direction_changes,
    ]
    colors_metrics = ["red", "green", "blue", "orange"]

    bars = axes[1, 1].bar(
        range(len(metrics)), values, color=colors_metrics, alpha=0.7, edgecolor="black"
    )

    # Add value labels on bars
    for bar, value in zip(bars, values):
        height = bar.get_height()
        axes[1, 1].text(
            bar.get_x() + bar.get_width() / 2.0,
            height + 0.1,
            f"{value:.2f}",
            ha="center",
            va="bottom",
            fontweight="bold",
        )

    axes[1, 1].set_title("Squiggliness Metrics 📊\n(Quantifying trajectory complexity)")
    axes[1, 1].set_xlabel("Metric Type")
    axes[1, 1].set_ylabel("Metric Value")
    axes[1, 1].set_xticks(range(len(metrics)))
    axes[1, 1].set_xticklabels(metrics, rotation=0)
    axes[1, 1].grid(True, alpha=0.3)

    plt.tight_layout()
    plt.savefig(
        "graphs/squiggliness_metrics.png", dpi=300, bbox_inches="tight"
    )
    plt.close()

    print("\n" + "=" * 70)
    print("🐍 WIND-VOCAB SQUIGGLE ANALYSIS RESULTS")
    print("=" * 70)
    print(f"📝 Sentence: {''.join([f'{token} ' for token in sentence_pattern])}")
    print(f"🌪️ Wind positions: {len(wind_positions)} steps")
    print(f"📊 Vocabulary range: {min(token_ids)} to {max(token_ids)}")
    print(f"🦘 Total vocabulary distance: {total_vocab_distance}")
    print(f"🌀 Embedding path length: {embedding_path_length:.2f}")
    print(f"💨 Hidden path length: {hidden_path_length:.2f}")
    print(f"🔄 Direction changes: {direction_changes}")
    print(f"📐 Average vocabulary jump: {np.mean(vocab_jumps):.2f}")
    print("=" * 70)
    print("Token sequence with IDs:")
    for i, (token, token_id) in enumerate(zip(sentence_pattern, token_ids)):
        print(f"  {i}: '{token}' (ID: {token_id})")
    print("=" * 70)


def visualize_3d_pca_with_time(embeddings, hidden_states, sentence_pattern, idx_to_token):
    """Create 3D visualization with front view (PCA perfect) and side view (using time as 3rd dimension)"""
    from mpl_toolkits.mplot3d import Axes3D
    import matplotlib.animation as animation
    from PIL import Image
    import io
    
    # Apply PCA to hidden states for 2D projection
    pca = PCA(n_components=2)
    hidden_2d = pca.fit_transform(hidden_states)
    
    # Time dimension (sequence position)
    time_positions = np.arange(len(sentence_pattern))
    
    # Create individual front view figure
    fig1 = plt.figure(figsize=(10, 10))
    ax1 = fig1.add_subplot(111, projection='3d')
    ax1.view_init(elev=0, azim=-90)  # Look from the side to see PC1 vs PC2
    
    # Plot trajectory in 3D space (Time, PC1, PC2)
    ax1.plot(time_positions, hidden_2d[:, 0], hidden_2d[:, 1], 
             'o-', linewidth=3, markersize=8, color='blue', alpha=0.8)
    
    # Add token labels
    for i, (t, x, y, token) in enumerate(zip(time_positions, hidden_2d[:, 0], hidden_2d[:, 1], sentence_pattern)):
        ax1.text(t, x, y, f'{i}:{token}', fontsize=10)
    
    ax1.set_xlabel('Time (Sequence Position)', fontsize=12)
    ax1.set_ylabel('PC1', fontsize=12)
    ax1.set_zlabel('PC2', fontsize=12)
    ax1.set_title('Front View: PCA Projection (Perfect)\nLooking at PC1 vs PC2 plane', fontsize=14)
    ax1.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('graphs/rnn_snake_front_view.png', dpi=300, bbox_inches='tight')
    plt.close()
    
    # Create individual side view figure
    fig2 = plt.figure(figsize=(10, 10))
    ax2 = fig2.add_subplot(111, projection='3d')
    ax2.view_init(elev=20, azim=-60)  # Angle to show time progression clearly
    
    # Plot trajectory with time on X-axis (left to right)
    ax2.plot(time_positions, hidden_2d[:, 0], hidden_2d[:, 1],
             'o-', linewidth=3, markersize=8, color='red', alpha=0.8)
    
    # Color gradient based on time
    colors = plt.cm.viridis(np.linspace(0, 1, len(time_positions)))
    ax2.scatter(time_positions, hidden_2d[:, 0], hidden_2d[:, 1],
                c=colors, s=100, edgecolor='black', linewidth=1, zorder=10)
    
    # Add vertical lines to show time progression
    for i in range(len(time_positions)):
        ax2.plot([time_positions[i], time_positions[i]], 
                 [hidden_2d[i, 0], hidden_2d[i, 0]], 
                 [0, hidden_2d[i, 1]], 
                 'gray', alpha=0.3, linestyle='--')
    
    # Add token labels
    for i, (t, x, y, token) in enumerate(zip(time_positions, hidden_2d[:, 0], hidden_2d[:, 1], sentence_pattern)):
        ax2.text(t, x, y, f'{token}', fontsize=10, ha='center')
    
    ax2.set_xlabel('Time (Sequence Position) →', fontsize=12)
    ax2.set_ylabel('PC1', fontsize=12)
    ax2.set_zlabel('PC2', fontsize=12)
    ax2.set_title('Side View: Time Flowing Left to Right\nShowing temporal evolution', fontsize=14)
    ax2.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('graphs/rnn_snake_side_view.png', dpi=300, bbox_inches='tight')
    plt.close()
    
    # Create animated GIF showing progression through time
    fig3 = plt.figure(figsize=(10, 10))
    ax3 = fig3.add_subplot(111, projection='3d')
    
    # Function to update the plot for each time step
    def animate_timestep(frame):
        ax3.clear()
        
        # Fixed view angle
        ax3.view_init(elev=20, azim=-60)
        
        # Calculate how many points to show (progressive reveal)
        current_step = min(frame + 1, len(time_positions))
        
        # Plot trajectory up to current time step
        if current_step > 1:
            ax3.plot(time_positions[:current_step], 
                    hidden_2d[:current_step, 0], 
                    hidden_2d[:current_step, 1],
                    'o-', linewidth=3, markersize=6, color='red', alpha=0.6)
        
        # Scatter plot with time-based colors for revealed points
        if current_step > 0:
            revealed_colors = plt.cm.viridis(np.linspace(0, 1, current_step))
            ax3.scatter(time_positions[:current_step], 
                       hidden_2d[:current_step, 0], 
                       hidden_2d[:current_step, 1],
                       c=revealed_colors, s=80, edgecolor='black', linewidth=1, zorder=10)
        
        # Highlight current point with larger marker
        if 0 < current_step <= len(time_positions):
            ax3.scatter([time_positions[current_step-1]], 
                       [hidden_2d[current_step-1, 0]], 
                       [hidden_2d[current_step-1, 1]],
                       c='yellow', s=200, edgecolor='red', linewidth=3, zorder=20,
                       marker='*')
        
        # Add vertical lines for revealed points
        for i in range(current_step):
            ax3.plot([time_positions[i], time_positions[i]], 
                     [hidden_2d[i, 0], hidden_2d[i, 0]], 
                     [0, hidden_2d[i, 1]], 
                     'gray', alpha=0.2, linestyle='--')
        
        # Add token labels for revealed points
        for i in range(current_step):
            t, x, y, token = time_positions[i], hidden_2d[i, 0], hidden_2d[i, 1], sentence_pattern[i]
            ax3.text(t, x, y, f'{token}', fontsize=10, ha='center',
                    fontweight='bold' if i == current_step-1 else 'normal')
        
        # Set fixed axis limits to prevent jumping
        ax3.set_xlim(-0.5, len(time_positions) - 0.5)
        ax3.set_ylim(hidden_2d[:, 0].min() - 1, hidden_2d[:, 0].max() + 1)
        ax3.set_zlim(hidden_2d[:, 1].min() - 1, hidden_2d[:, 1].max() + 1)
        
        ax3.set_xlabel('Time (Sequence Position) →', fontsize=12)
        ax3.set_ylabel('PC1', fontsize=12)
        ax3.set_zlabel('PC2', fontsize=12)
        
        # Update title with current token
        if 0 < current_step <= len(time_positions):
            current_token = sentence_pattern[current_step-1]
            ax3.set_title(f'RNN Snake: Time Step {current_step}/{len(time_positions)}\nCurrent Token: "{current_token}"', 
                         fontsize=14, fontweight='bold')
        else:
            ax3.set_title(f'RNN Snake: Initializing...', fontsize=14)
        
        ax3.grid(True, alpha=0.3)
        
        return ax3,
    
    # Create animation with pause at beginning and end
    total_frames = len(time_positions) + 10  # Add extra frames for pause
    
    def frame_generator(f):
        if f < 5:  # Pause at start
            return 0
        elif f < 5 + len(time_positions):  # Animate through time
            return f - 4
        else:  # Pause at end
            return len(time_positions)
    
    anim = animation.FuncAnimation(fig3, lambda f: animate_timestep(frame_generator(f)), 
                                  frames=total_frames, interval=300, blit=False)
    
    # Save as GIF
    anim.save('graphs/rnn_snake_timestep.gif', writer='pillow', fps=3, dpi=100)
    plt.close()
    
    print("\n3D Visualizations saved:")
    print("- graphs/rnn_snake_front_view.png - Front view (PCA projection)")
    print("- graphs/rnn_snake_side_view.png - Side view (time flowing left to right)")
    print("- graphs/rnn_snake_timestep.gif - Animated progression through time steps")


def main():
    """Main function for wind-vocab trajectory analysis"""
    print("=" * 70)
    print("🌪️ WIND LANES vs VOCABULARY: Single Long Squiggly Trajectory")
    print("=" * 70)

    # Create simple data
    data, token_to_idx, idx_to_token, sentence_pattern = create_simple_sentence()

    print(f"Vocabulary: {list(idx_to_token.values())}")
    print(f"Sentence: {' '.join(sentence_pattern)}")
    print(f"Sequence length: {len(sentence_pattern)} tokens")

    # Create model
    model = SimpleRNN(vocab_size=5, embedding_dim=16, hidden_dim=32)

    print(f"\nModel parameters: {sum(p.numel() for p in model.parameters()):,}")

    # Train model
    trained_model = train_simple_model(model, data, epochs=300)

    # Get final trajectory data
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    trained_model.eval()
    sequence = data[0].to(device)

    with torch.no_grad():
        logits = trained_model(sequence.unsqueeze(0))
        embeddings = trained_model.embedding_trajectory
        hidden_states = trained_model.hidden_trajectory

    # Visualize the wind-vocab trajectory
    print("\nAnalyzing wind-vocab trajectory...")
    wind_positions, token_ids, _ = visualize_wind_vocab_trajectory(
        trained_model, data, idx_to_token, sentence_pattern
    )

    # Analyze squiggliness metrics
    print("Computing squiggliness metrics...")
    analyze_squiggliness_metrics(
        wind_positions, token_ids, sentence_pattern, embeddings, hidden_states, idx_to_token
    )
    
    # Create 3D visualization with front and side views
    print("\nCreating 3D visualization with front (PCA) and side (time) views...")
    visualize_3d_pca_with_time(embeddings, hidden_states, sentence_pattern, idx_to_token)

    print("\n" + "=" * 70)
    print("Analysis complete! Generated files:")
    print(
        "1. graphs/wind_vocab_trajectory.png - Main trajectory visualization"
    )
    print("2. graphs/squiggliness_metrics.png - Complexity analysis")
    print("3. graphs/rnn_snake_3d_views.png - 3D views (PCA front, time side)")
    print("=" * 70)
    print("Key insights:")
    print("🌪️ X-axis = Wind position (time through sequence)")
    print("📝 Y-axis = Vocabulary tokens (discrete word choices)")
    print("🐍 Trajectory = Single long squiggly line through wind-vocab space")
    print("💨 Wind strength = Hidden state dynamics")
    print("🦘 Jump sizes = Vocabulary transition distances")
    print("📊 3D views = Front (PCA perfect) and Side (time evolution)")
    print("=" * 70)


if __name__ == "__main__":
    main()
