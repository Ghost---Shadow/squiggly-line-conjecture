import torch
import torch.nn as nn
import torch.optim as optim
import numpy as np
import matplotlib.pyplot as plt
from sklearn.decomposition import PCA
import os
import math

# Disable interactive plotting
plt.ioff()

# Set random seeds
torch.manual_seed(42)
np.random.seed(42)

# Create output directory
os.makedirs("graphs", exist_ok=True)


class PositionalEncoding(nn.Module):
    def __init__(self, d_model, max_len=5000):
        super(PositionalEncoding, self).__init__()
        pe = torch.zeros(max_len, d_model)
        position = torch.arange(0, max_len, dtype=torch.float).unsqueeze(1)
        div_term = torch.exp(torch.arange(0, d_model, 2).float() * (-math.log(10000.0) / d_model))
        pe[:, 0::2] = torch.sin(position * div_term)
        pe[:, 1::2] = torch.cos(position * div_term)
        self.register_buffer('pe', pe)

    def forward(self, x):
        seq_len = x.size(1)
        return x + self.pe[:seq_len].unsqueeze(0)


class SimpleTransformer(nn.Module):
    def __init__(self, vocab_size, embedding_dim=16, hidden_dim=32, num_heads=4, num_layers=2):
        super(SimpleTransformer, self).__init__()
        self.vocab_size = vocab_size
        self.embedding_dim = embedding_dim
        self.hidden_dim = hidden_dim
        self.num_heads = num_heads
        self.num_layers = num_layers
        
        # Token embedding layer
        self.embedding = nn.Embedding(vocab_size, embedding_dim)
        
        # Positional encoding
        self.pos_encoding = PositionalEncoding(embedding_dim)
        
        # Custom self-attention layers for visibility into attention weights
        self.attention_layers = nn.ModuleList()
        self.norm_layers = nn.ModuleList()
        self.ffn_layers = nn.ModuleList()
        self.norm2_layers = nn.ModuleList()
        
        for _ in range(num_layers):
            # Multi-head attention
            self.attention_layers.append(
                nn.MultiheadAttention(embedding_dim, num_heads, batch_first=True, dropout=0.1)
            )
            self.norm_layers.append(nn.LayerNorm(embedding_dim))
            
            # Feed-forward network
            self.ffn_layers.append(nn.Sequential(
                nn.Linear(embedding_dim, hidden_dim),
                nn.ReLU(),
                nn.Dropout(0.1),
                nn.Linear(hidden_dim, embedding_dim)
            ))
            self.norm2_layers.append(nn.LayerNorm(embedding_dim))
        
        # Output projection
        self.output_projection = nn.Linear(embedding_dim, vocab_size)
        
        # Store trajectories and attention weights
        self.embedding_trajectory = None
        self.hidden_trajectory = None
        self.attention_weights = []
    
    def forward(self, x):
        batch_size, seq_len = x.size()
        
        # Clear previous attention weights
        self.attention_weights = []
        
        # Get embeddings
        embeddings = self.embedding(x)
        self.embedding_trajectory = embeddings.detach().cpu().numpy()[0]  # First batch
        
        # Add positional encoding
        hidden = self.pos_encoding(embeddings)
        
        # Create causal mask for autoregressive generation
        mask = nn.Transformer.generate_square_subsequent_mask(seq_len).to(x.device)
        
        # Process through transformer layers manually
        for i in range(self.num_layers):
            # Self-attention with residual connection
            attn_out, attn_weights = self.attention_layers[i](
                hidden, hidden, hidden, 
                attn_mask=mask,
                need_weights=True,
                average_attn_weights=True
            )
            hidden = self.norm_layers[i](hidden + attn_out)
            
            # Store attention weights
            if attn_weights is not None:
                self.attention_weights.append(attn_weights)
            
            # Feed-forward with residual connection
            ffn_out = self.ffn_layers[i](hidden)
            hidden = self.norm2_layers[i](hidden + ffn_out)
        
        self.hidden_trajectory = hidden.detach().cpu().numpy()[0]  # First batch
        
        # Output logits
        logits = self.output_projection(hidden)
        
        return logits
    
    def get_attention_matrix(self):
        """Get the average attention matrix across all heads and layers"""
        if not self.attention_weights:
            return None
        
        # Average across all layers
        # Each weight is shape: (batch, seq_len, seq_len)
        avg_attention = torch.stack(self.attention_weights).mean(dim=0)
        return avg_attention[0].detach().cpu().numpy()  # Return first batch


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


def train_transformer_model(model, data, epochs=200):
    """Train the transformer on the simple sentence"""
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    model.to(device)
    data = data.to(device)
    
    criterion = nn.CrossEntropyLoss()
    optimizer = optim.Adam(model.parameters(), lr=0.005)
    scheduler = optim.lr_scheduler.CosineAnnealingLR(optimizer, T_max=epochs)
    
    print("Training transformer on basic sentence...")
    for epoch in range(epochs):
        model.train()
        
        inputs = data[:, :-1]  # All except last token
        targets = data[:, 1:]  # All except first token
        
        optimizer.zero_grad()
        logits = model(inputs)
        
        loss = criterion(logits.reshape(-1, model.vocab_size), targets.reshape(-1))
        loss.backward()
        
        # Gradient clipping for stability
        torch.nn.utils.clip_grad_norm_(model.parameters(), max_norm=1.0)
        
        optimizer.step()
        scheduler.step()
        
        if epoch % 40 == 0:
            print(f"Epoch {epoch}/{epochs}, Loss: {loss.item():.4f}")
    
    print("Training completed!")
    return model


def visualize_transformer_attention_trajectory(model, data, idx_to_token, sentence_pattern):
    """Visualize trajectory with attention mechanisms highlighted"""
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    model.eval()
    
    sequence = data[0].to(device)
    
    with torch.no_grad():
        # Forward pass
        logits = model(sequence.unsqueeze(0))
        
        # Get trajectories
        embeddings = model.embedding_trajectory  # Shape: (seq_len, embedding_dim)
        hidden_states = model.hidden_trajectory  # Shape: (seq_len, hidden_dim)
        attention_matrix = model.get_attention_matrix()  # Shape: (seq_len, seq_len)
    
    seq_len = len(sentence_pattern)
    
    # Create figure with transformer-specific visualizations
    fig, axes = plt.subplots(2, 3, figsize=(18, 12))
    fig.suptitle(
        "⚡ Transformer Attention Snake: Self-Attention Language Trajectory",
        fontsize=16,
    )
    
    # 1. Main plot: Wind position (x) vs Token ID (y) with attention intensity
    wind_positions = range(seq_len)  # Time/position along sequence
    token_ids = [sequence[i].item() for i in range(seq_len)]
    
    # Use attention strengths to modulate line appearance
    if attention_matrix is not None:
        # Get self-attention strength (diagonal of attention matrix)
        self_attention = np.diag(attention_matrix)
        line_widths = 2 + 8 * self_attention  # Scale line width by attention
    else:
        line_widths = [4] * (seq_len - 1)
    
    # Plot with varying line widths based on attention
    for i in range(len(wind_positions) - 1):
        axes[0, 0].plot(
            wind_positions[i:i+2],
            token_ids[i:i+2],
            "-",
            linewidth=line_widths[i] if i < len(line_widths) else 4,
            color=plt.cm.plasma(i / seq_len),
            alpha=0.8,
        )
    
    axes[0, 0].scatter(
        wind_positions,
        token_ids,
        s=200,
        c=range(seq_len),
        cmap="plasma",
        edgecolor="black",
        linewidth=2,
        zorder=10
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
        "Transformer Token Trajectory ⚡📝\n(Line width = attention strength)"
    )
    axes[0, 0].set_xlabel("Sequence Position")
    axes[0, 0].set_ylabel("Vocabulary Token ID")
    axes[0, 0].set_yticks(range(len(idx_to_token)))
    axes[0, 0].set_yticklabels([idx_to_token[i] for i in range(len(idx_to_token))])
    axes[0, 0].grid(True, alpha=0.3)
    
    # 2. Attention heatmap
    if attention_matrix is not None:
        im = axes[0, 1].imshow(
            attention_matrix,
            cmap="hot",
            aspect="auto",
            interpolation="nearest"
        )
        axes[0, 1].set_title("Self-Attention Heatmap 🔥\n(Where tokens look)")
        axes[0, 1].set_xlabel("Key Position")
        axes[0, 1].set_ylabel("Query Position")
        
        # Add token labels
        axes[0, 1].set_xticks(range(seq_len))
        axes[0, 1].set_xticklabels(sentence_pattern, rotation=45, ha="right")
        axes[0, 1].set_yticks(range(seq_len))
        axes[0, 1].set_yticklabels(sentence_pattern)
        plt.colorbar(im, ax=axes[0, 1])
    else:
        axes[0, 1].text(0.5, 0.5, "No attention weights captured", 
                        ha="center", va="center", transform=axes[0, 1].transAxes)
    
    # 3. Hidden state energy (transformer output magnitude)
    hidden_energy = np.linalg.norm(hidden_states, axis=1)
    
    axes[0, 2].plot(
        wind_positions,
        hidden_energy,
        "D-",
        linewidth=3,
        markersize=8,
        color="purple",
        alpha=0.8,
        label="Transformer Energy",
    )
    axes[0, 2].fill_between(wind_positions, hidden_energy, alpha=0.3, color="purple")
    
    # Mark high energy points
    high_energy_threshold = np.percentile(hidden_energy, 75)
    high_energy_points = [i for i, e in enumerate(hidden_energy) if e > high_energy_threshold]
    
    for point in high_energy_points:
        axes[0, 2].axvline(x=point, color="orange", alpha=0.7, linestyle="--")
        axes[0, 2].text(
            point,
            hidden_energy[point],
            sentence_pattern[point],
            rotation=90,
            fontsize=8,
            ha="right",
            va="bottom",
        )
    
    axes[0, 2].set_title("Transformer Output Energy ⚡\n(Hidden state magnitude)")
    axes[0, 2].set_xlabel("Sequence Position")
    axes[0, 2].set_ylabel("Energy Level")
    axes[0, 2].grid(True, alpha=0.3)
    axes[0, 2].legend()
    
    # 4. Attention flow visualization
    if attention_matrix is not None:
        # Show strongest attention connections for each position
        axes[1, 0].set_xlim(-0.5, seq_len - 0.5)
        axes[1, 0].set_ylim(-0.5, seq_len - 0.5)
        
        # Plot attention flows as arrows
        for i in range(seq_len):
            for j in range(i + 1):  # Causal mask
                attention_strength = attention_matrix[i, j]
                if attention_strength > 0.1:  # Threshold for visibility
                    axes[1, 0].arrow(
                        j, i, 0, 0,
                        head_width=0.2,
                        head_length=0.1,
                        fc=plt.cm.plasma(attention_strength),
                        ec=plt.cm.plasma(attention_strength),
                        alpha=min(attention_strength * 2, 1.0),
                        linewidth=attention_strength * 5
                    )
        
        # Add token positions
        for i in range(seq_len):
            axes[1, 0].scatter(i, i, s=300, c="white", edgecolor="black", linewidth=2, zorder=10)
            axes[1, 0].text(i, i, sentence_pattern[i], ha="center", va="center", fontsize=9, fontweight="bold")
        
        axes[1, 0].set_title("Attention Flow Network 🌐\n(Strength of connections)")
        axes[1, 0].set_xlabel("Source Position")
        axes[1, 0].set_ylabel("Target Position")
        axes[1, 0].invert_yaxis()
        axes[1, 0].grid(True, alpha=0.3)
    else:
        axes[1, 0].text(0.5, 0.5, "No attention flow data", 
                       ha="center", va="center", transform=axes[1, 0].transAxes)
    
    # 5. Embedding space trajectory (2D PCA)
    pca_emb = PCA(n_components=2)
    embeddings_2d = pca_emb.fit_transform(embeddings)
    
    # Plot embedding trajectory with gradient colors
    for i in range(len(embeddings_2d) - 1):
        axes[1, 1].plot(
            embeddings_2d[i:i+2, 0],
            embeddings_2d[i:i+2, 1],
            "-",
            linewidth=3,
            color=plt.cm.viridis(i / len(embeddings_2d)),
            alpha=0.8
        )
    
    axes[1, 1].scatter(
        embeddings_2d[:, 0],
        embeddings_2d[:, 1],
        c=range(len(embeddings_2d)),
        cmap="viridis",
        s=150,
        edgecolor="black",
        linewidth=1,
        zorder=10
    )
    
    # Add token labels
    for i, (point, token) in enumerate(zip(embeddings_2d, sentence_pattern)):
        axes[1, 1].annotate(
            f"{i}:{token}",
            point,
            xytext=(5, 5),
            textcoords="offset points",
            fontsize=8,
            ha="left",
            va="bottom",
            bbox=dict(boxstyle="round,pad=0.3", facecolor="lightblue", alpha=0.7),
        )
    
    axes[1, 1].set_title("Embedding Space Snake 🐍\n(2D projection of embeddings)")
    axes[1, 1].set_xlabel("Embedding PC1")
    axes[1, 1].set_ylabel("Embedding PC2")
    axes[1, 1].grid(True, alpha=0.3)
    
    # 6. Positional encoding influence
    # Show how positional encodings affect the trajectory
    pos_encodings = model.pos_encoding.pe[:seq_len].detach().cpu().numpy()
    pca_pos = PCA(n_components=1)
    pos_influence = pca_pos.fit_transform(pos_encodings).flatten()
    
    axes[1, 2].plot(
        wind_positions,
        pos_influence,
        "s-",
        linewidth=3,
        markersize=8,
        color="green",
        alpha=0.8,
        label="Position Signal",
    )
    
    # Overlay with token changes
    ax2 = axes[1, 2].twinx()
    ax2.plot(
        wind_positions,
        token_ids,
        "o--",
        linewidth=2,
        markersize=6,
        color="red",
        alpha=0.6,
        label="Token IDs",
    )
    
    axes[1, 2].set_title("Positional Encoding vs Tokens 📍\n(How position affects trajectory)")
    axes[1, 2].set_xlabel("Sequence Position")
    axes[1, 2].set_ylabel("Position Encoding (PC1)", color="green")
    ax2.set_ylabel("Token ID", color="red")
    axes[1, 2].tick_params(axis='y', labelcolor='green')
    ax2.tick_params(axis='y', labelcolor='red')
    axes[1, 2].grid(True, alpha=0.3)
    axes[1, 2].legend(loc="upper left")
    ax2.legend(loc="upper right")
    
    plt.tight_layout()
    plt.savefig(
        "graphs/transformer_attention_trajectory.png",
        dpi=300,
        bbox_inches="tight",
    )
    plt.close()
    
    return wind_positions, token_ids, sentence_pattern, attention_matrix


def analyze_transformer_vs_rnn_patterns(
    wind_positions, token_ids, sentence_pattern, embeddings, hidden_states, 
    idx_to_token, attention_matrix
):
    """Analyze transformer-specific patterns vs RNN behavior"""
    
    fig, axes = plt.subplots(2, 2, figsize=(16, 12))
    fig.suptitle("⚡ Transformer vs RNN: Pattern Analysis", fontsize=16)
    
    # 1. Attention distance analysis
    if attention_matrix is not None:
        attention_distances = []
        for i in range(len(attention_matrix)):
            # Calculate weighted average distance of attention
            weights = attention_matrix[i, :i+1]  # Causal mask
            positions = np.arange(i+1)
            if weights.sum() > 0:
                avg_distance = np.sum(weights * np.abs(i - positions)) / weights.sum()
                attention_distances.append(avg_distance)
            else:
                attention_distances.append(0)
        
        axes[0, 0].bar(
            range(len(attention_distances)),
            attention_distances,
            color="purple",
            alpha=0.7,
            edgecolor="black",
        )
        
        # Add token labels
        for i, (dist, token) in enumerate(zip(attention_distances, sentence_pattern)):
            if dist > np.mean(attention_distances):
                axes[0, 0].text(
                    i, dist + 0.1, token, rotation=45, fontsize=8, ha="left", va="bottom"
                )
        
        axes[0, 0].set_title("Attention Look-back Distance 👀\n(How far back tokens attend)")
        axes[0, 0].set_xlabel("Token Position")
        axes[0, 0].set_ylabel("Average Attention Distance")
        axes[0, 0].grid(True, alpha=0.3)
    
    # 2. Information bottleneck analysis
    # Measure information flow through layers
    hidden_variance = np.var(hidden_states, axis=1)
    embedding_variance = np.var(embeddings, axis=1)
    
    axes[0, 1].plot(
        wind_positions,
        embedding_variance,
        "o-",
        linewidth=2,
        markersize=6,
        color="blue",
        alpha=0.8,
        label="Embedding Variance",
    )
    axes[0, 1].plot(
        wind_positions,
        hidden_variance,
        "s-",
        linewidth=2,
        markersize=6,
        color="red",
        alpha=0.8,
        label="Output Variance",
    )
    
    axes[0, 1].fill_between(
        wind_positions, embedding_variance, hidden_variance, 
        where=(hidden_variance >= embedding_variance),
        color="green", alpha=0.3, label="Information Gain"
    )
    axes[0, 1].fill_between(
        wind_positions, embedding_variance, hidden_variance,
        where=(hidden_variance < embedding_variance),
        color="orange", alpha=0.3, label="Information Loss"
    )
    
    axes[0, 1].set_title("Information Flow Analysis 📊\n(Variance as proxy for information)")
    axes[0, 1].set_xlabel("Sequence Position")
    axes[0, 1].set_ylabel("Variance")
    axes[0, 1].legend()
    axes[0, 1].grid(True, alpha=0.3)
    
    # 3. Trajectory smoothness comparison
    # Calculate trajectory smoothness (second derivative)
    token_velocities = np.diff(token_ids)
    token_accelerations = np.diff(token_velocities) if len(token_velocities) > 0 else []
    
    if len(token_accelerations) > 0:
        axes[1, 0].plot(
            range(len(token_accelerations)),
            token_accelerations,
            "^-",
            linewidth=3,
            markersize=8,
            color="orange",
            alpha=0.8,
            label="Acceleration",
        )
        axes[1, 0].axhline(y=0, color="black", linestyle="-", alpha=0.3)
        axes[1, 0].fill_between(
            range(len(token_accelerations)),
            token_accelerations,
            alpha=0.3,
            color="orange"
        )
        
        # Mark sharp turns
        sharp_turns = np.where(np.abs(token_accelerations) > 1)[0]
        for turn in sharp_turns:
            axes[1, 0].axvline(x=turn, color="red", alpha=0.5, linestyle="--")
            if turn < len(sentence_pattern) - 2:
                axes[1, 0].text(
                    turn, token_accelerations[turn],
                    f"{sentence_pattern[turn+1]}",
                    rotation=90, fontsize=8, ha="right"
                )
    
    axes[1, 0].set_title("Trajectory Smoothness 〰️\n(Acceleration = trajectory curvature)")
    axes[1, 0].set_xlabel("Position")
    axes[1, 0].set_ylabel("Token Acceleration")
    axes[1, 0].legend()
    axes[1, 0].grid(True, alpha=0.3)
    
    # 4. Attention entropy analysis
    if attention_matrix is not None:
        attention_entropy = []
        for i in range(len(attention_matrix)):
            row = attention_matrix[i, :i+1]  # Causal mask
            if len(row) > 0 and row.sum() > 0:
                # Normalize to probability distribution
                prob = row / row.sum()
                # Calculate entropy
                entropy = -np.sum(prob * np.log(prob + 1e-10))
                attention_entropy.append(entropy)
            else:
                attention_entropy.append(0)
        
        axes[1, 1].plot(
            range(len(attention_entropy)),
            attention_entropy,
            "D-",
            linewidth=3,
            markersize=8,
            color="purple",
            alpha=0.8,
        )
        axes[1, 1].fill_between(
            range(len(attention_entropy)),
            attention_entropy,
            alpha=0.3,
            color="purple"
        )
        
        # Mark low entropy (focused attention) points
        low_entropy_threshold = np.percentile(attention_entropy, 25)
        focused_points = [i for i, e in enumerate(attention_entropy) if e < low_entropy_threshold and e > 0]
        
        for point in focused_points:
            axes[1, 1].axvline(x=point, color="green", alpha=0.5, linestyle="--")
            axes[1, 1].text(
                point, attention_entropy[point],
                sentence_pattern[point],
                rotation=90, fontsize=8, ha="right", va="bottom"
            )
        
        axes[1, 1].set_title("Attention Entropy 🎯\n(Low = focused, High = distributed)")
        axes[1, 1].set_xlabel("Token Position")
        axes[1, 1].set_ylabel("Entropy")
        axes[1, 1].grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig(
        "graphs/transformer_pattern_analysis.png",
        dpi=300,
        bbox_inches="tight"
    )
    plt.close()
    
    print("\n" + "=" * 70)
    print("⚡ TRANSFORMER SNAKE ANALYSIS RESULTS")
    print("=" * 70)
    print(f"📝 Sentence: {' '.join(sentence_pattern)}")
    print(f"🌐 Sequence length: {len(sentence_pattern)} tokens")
    print(f"📊 Vocabulary range: {min(token_ids)} to {max(token_ids)}")
    
    if attention_matrix is not None:
        avg_attention_distance = np.mean([
            np.sum(attention_matrix[i, :i+1] * np.abs(i - np.arange(i+1))) / attention_matrix[i, :i+1].sum()
            if attention_matrix[i, :i+1].sum() > 0 else 0
            for i in range(len(attention_matrix))
        ])
        print(f"👀 Average attention distance: {avg_attention_distance:.2f}")
        
        max_attention_per_pos = [
            np.max(attention_matrix[i, :i+1]) if i > 0 else attention_matrix[0, 0]
            for i in range(len(attention_matrix))
        ]
        print(f"🎯 Max attention strength range: {min(max_attention_per_pos):.3f} to {max(max_attention_per_pos):.3f}")
    
    print(f"⚡ Hidden state energy range: {np.linalg.norm(hidden_states, axis=1).min():.2f} to {np.linalg.norm(hidden_states, axis=1).max():.2f}")
    print("=" * 70)


def visualize_3d_transformer_attention(embeddings, hidden_states, sentence_pattern, idx_to_token, attention_matrix):
    """Create 3D visualization with attention-weighted connections"""
    from mpl_toolkits.mplot3d import Axes3D
    import matplotlib.animation as animation
    
    # Apply PCA to hidden states for 2D projection
    pca = PCA(n_components=2)
    hidden_2d = pca.fit_transform(hidden_states)
    
    # Time dimension (sequence position)
    time_positions = np.arange(len(sentence_pattern))
    
    # Create 3D visualization with attention connections
    fig = plt.figure(figsize=(15, 10))
    ax = fig.add_subplot(111, projection='3d')
    
    # Plot main trajectory
    ax.plot(time_positions, hidden_2d[:, 0], hidden_2d[:, 1], 
            'o-', linewidth=3, markersize=8, color='blue', alpha=0.8)
    
    # Add attention connections as semi-transparent lines
    if attention_matrix is not None:
        for i in range(len(time_positions)):
            for j in range(i):
                attention_strength = attention_matrix[i, j]
                if attention_strength > 0.1:  # Threshold for visibility
                    ax.plot([time_positions[j], time_positions[i]], 
                           [hidden_2d[j, 0], hidden_2d[i, 0]], 
                           [hidden_2d[j, 1], hidden_2d[i, 1]],
                           color='red', alpha=attention_strength * 0.5, 
                           linewidth=attention_strength * 3)
    
    # Color gradient based on time
    colors = plt.cm.plasma(np.linspace(0, 1, len(time_positions)))
    ax.scatter(time_positions, hidden_2d[:, 0], hidden_2d[:, 1],
               c=colors, s=150, edgecolor='black', linewidth=2, zorder=10)
    
    # Add token labels
    for i, (t, x, y, token) in enumerate(zip(time_positions, hidden_2d[:, 0], hidden_2d[:, 1], sentence_pattern)):
        ax.text(t, x, y, f'{token}', fontsize=10, ha='center', fontweight='bold')
    
    ax.set_xlabel('Time (Sequence Position) →', fontsize=12)
    ax.set_ylabel('Hidden PC1', fontsize=12)
    ax.set_zlabel('Hidden PC2', fontsize=12)
    ax.set_title('Transformer Snake with Attention Connections\n(Red lines = attention strength)', fontsize=14)
    ax.view_init(elev=20, azim=-60)
    ax.grid(True, alpha=0.3)
    
    plt.tight_layout()
    plt.savefig('graphs/transformer_snake_3d_attention.png', dpi=300, bbox_inches='tight')
    plt.close()
    
    # Create animated version showing attention flow
    fig2 = plt.figure(figsize=(12, 10))
    ax2 = fig2.add_subplot(111, projection='3d')
    
    def animate_attention(frame):
        ax2.clear()
        ax2.view_init(elev=20, azim=-60 + frame * 2)  # Rotate view
        
        # Plot trajectory
        ax2.plot(time_positions, hidden_2d[:, 0], hidden_2d[:, 1],
                'o-', linewidth=2, markersize=6, color='blue', alpha=0.6)
        
        # Highlight current position
        current_pos = frame % len(time_positions)
        ax2.scatter([time_positions[current_pos]], 
                   [hidden_2d[current_pos, 0]], 
                   [hidden_2d[current_pos, 1]],
                   c='yellow', s=300, edgecolor='red', linewidth=3, 
                   marker='*', zorder=20)
        
        # Show attention from current position
        if attention_matrix is not None and current_pos > 0:
            for j in range(current_pos):
                attention_strength = attention_matrix[current_pos, j]
                if attention_strength > 0.05:
                    ax2.plot([time_positions[j], time_positions[current_pos]], 
                            [hidden_2d[j, 0], hidden_2d[current_pos, 0]], 
                            [hidden_2d[j, 1], hidden_2d[current_pos, 1]],
                            color='red', alpha=min(attention_strength, 0.8), 
                            linewidth=attention_strength * 5)
        
        # Add all points
        for i in range(len(time_positions)):
            color = 'yellow' if i == current_pos else plt.cm.plasma(i/len(time_positions))
            ax2.scatter([time_positions[i]], [hidden_2d[i, 0]], [hidden_2d[i, 1]],
                       c=[color], s=100, edgecolor='black', linewidth=1, zorder=10)
        
        # Add labels
        for i, (t, x, y, token) in enumerate(zip(time_positions, hidden_2d[:, 0], hidden_2d[:, 1], sentence_pattern)):
            fontweight = 'bold' if i == current_pos else 'normal'
            ax2.text(t, x, y, f'{token}', fontsize=9, ha='center', fontweight=fontweight)
        
        ax2.set_xlabel('Time →', fontsize=11)
        ax2.set_ylabel('PC1', fontsize=11)
        ax2.set_zlabel('PC2', fontsize=11)
        ax2.set_title(f'Transformer Attention Flow\nPosition {current_pos}: "{sentence_pattern[current_pos]}"', 
                     fontsize=13)
        ax2.grid(True, alpha=0.3)
        
        return ax2,
    
    anim = animation.FuncAnimation(fig2, animate_attention, 
                                  frames=len(time_positions) * 2, 
                                  interval=500, blit=False)
    
    anim.save('graphs/transformer_snake_attention_flow.gif', writer='pillow', fps=2, dpi=80)
    plt.close()
    
    print("\n3D Transformer visualizations saved:")
    print("- graphs/transformer_snake_3d_attention.png - 3D view with attention connections")
    print("- graphs/transformer_snake_attention_flow.gif - Animated attention flow")


def main():
    """Main function for transformer snake analysis"""
    print("=" * 70)
    print("⚡ TRANSFORMER ATTENTION SNAKE: Self-Attention Language Trajectory")
    print("=" * 70)
    
    # Create simple data
    data, token_to_idx, idx_to_token, sentence_pattern = create_simple_sentence()
    
    print(f"Vocabulary: {list(idx_to_token.values())}")
    print(f"Sentence: {' '.join(sentence_pattern)}")
    print(f"Sequence length: {len(sentence_pattern)} tokens")
    
    # Create transformer model
    model = SimpleTransformer(
        vocab_size=5, 
        embedding_dim=16, 
        hidden_dim=32,
        num_heads=4,
        num_layers=2
    )
    
    print(f"\nModel parameters: {sum(p.numel() for p in model.parameters()):,}")
    print(f"Architecture: {model.num_heads} heads, {model.num_layers} layers")
    
    # Train model
    trained_model = train_transformer_model(model, data, epochs=300)
    
    # Get final trajectory data
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    trained_model.eval()
    sequence = data[0].to(device)
    
    with torch.no_grad():
        logits = trained_model(sequence.unsqueeze(0))
        embeddings = trained_model.embedding_trajectory
        hidden_states = trained_model.hidden_trajectory
        attention_matrix = trained_model.get_attention_matrix()
    
    # Visualize the transformer trajectory with attention
    print("\nAnalyzing transformer attention trajectory...")
    wind_positions, token_ids, _, attention_matrix = visualize_transformer_attention_trajectory(
        trained_model, data, idx_to_token, sentence_pattern
    )
    
    # Analyze transformer-specific patterns
    print("Computing transformer pattern analysis...")
    analyze_transformer_vs_rnn_patterns(
        wind_positions, token_ids, sentence_pattern, embeddings, hidden_states, 
        idx_to_token, attention_matrix
    )
    
    # Create 3D visualization with attention connections
    print("\nCreating 3D visualization with attention connections...")
    visualize_3d_transformer_attention(
        embeddings, hidden_states, sentence_pattern, idx_to_token, attention_matrix
    )
    
    print("\n" + "=" * 70)
    print("Analysis complete! Generated files:")
    print("1. graphs/transformer_attention_trajectory.png - Main trajectory with attention")
    print("2. graphs/transformer_pattern_analysis.png - Pattern analysis vs RNN")
    print("3. graphs/transformer_snake_3d_attention.png - 3D view with attention")
    print("4. graphs/transformer_snake_attention_flow.gif - Animated attention flow")
    print("=" * 70)
    print("Key insights:")
    print("⚡ Self-attention allows looking back at any previous position")
    print("🎯 Attention patterns show where model focuses")
    print("🌐 Transformer can model long-range dependencies")
    print("📊 Different trajectory dynamics compared to RNN")
    print("🐍 Snake trajectory influenced by attention weights")
    print("=" * 70)


if __name__ == "__main__":
    main()