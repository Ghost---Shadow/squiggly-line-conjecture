import torch
import torch.nn as nn
import torch.optim as optim
from torchvision import datasets, transforms
import matplotlib.pyplot as plt
import matplotlib.animation as animation
import numpy as np
from sklearn.decomposition import PCA
from sklearn.manifold import TSNE
import seaborn as sns
import os
from PIL import Image

# Disable interactive plotting
plt.ioff()

# Set random seeds for reproducibility
torch.manual_seed(42)
np.random.seed(42)

# Create output directory
os.makedirs('graphs', exist_ok=True)

class SnakeNet(nn.Module):
    def __init__(self, input_size=784, hidden_sizes=[512, 256, 128, 64], num_classes=10):
        super(SnakeNet, self).__init__()
        
        # Store layer dimensions for analysis
        self.layer_dims = [input_size] + hidden_sizes + [num_classes]
        
        # Build the network
        layers = []
        prev_size = input_size
        
        for i, hidden_size in enumerate(hidden_sizes):
            layers.append(nn.Linear(prev_size, hidden_size))
            layers.append(nn.ReLU())
            layers.append(nn.Dropout(0.2))  # Add dropout for regularization
            prev_size = hidden_size
            
        # Final layer (no ReLU after output)
        layers.append(nn.Linear(prev_size, num_classes))
        
        self.network = nn.Sequential(*layers)
        
        # Store intermediate layers for analysis
        self.layers = []
        for i, layer in enumerate(self.network):
            if isinstance(layer, nn.Linear):
                self.layers.append(layer)
    
    def forward(self, x):
        x = x.view(x.size(0), -1)  # Flatten input
        return self.network(x)
    
    def get_intermediate_activations(self, x):
        """Get activations at each layer for analysis"""
        activations = []
        current = x.view(x.size(0), -1)  # Flatten input
        activations.append(current.detach().cpu().numpy())
        
        layer_idx = 0
        for module in self.network:
            current = module(current)
            if isinstance(module, nn.ReLU):
                activations.append(current.detach().cpu().numpy())
                layer_idx += 1
                
        return activations

def load_mnist_data():
    """Load MNIST dataset"""
    transform = transforms.Compose([
        transforms.ToTensor(),
        transforms.Normalize((0.1307,), (0.3081,))
    ])
    
    train_dataset = datasets.MNIST('./data', train=True, download=True, transform=transform)
    test_dataset = datasets.MNIST('./data', train=False, transform=transform)
    
    train_loader = torch.utils.data.DataLoader(train_dataset, batch_size=64, shuffle=True)
    test_loader = torch.utils.data.DataLoader(test_dataset, batch_size=1000, shuffle=False)
    
    return train_loader, test_loader

def train_model(model, train_loader, test_loader, epochs=5):
    """Train the neural network"""
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    model.to(device)
    
    criterion = nn.CrossEntropyLoss()
    optimizer = optim.Adam(model.parameters(), lr=0.001)
    
    train_losses = []
    test_accuracies = []
    
    print("Training the neural network...")
    for epoch in range(epochs):
        # Training
        model.train()
        running_loss = 0.0
        for batch_idx, (data, target) in enumerate(train_loader):
            data, target = data.to(device), target.to(device)
            
            optimizer.zero_grad()
            output = model(data)
            loss = criterion(output, target)
            loss.backward()
            optimizer.step()
            
            running_loss += loss.item()
            
            if batch_idx % 100 == 0:
                print(f'Epoch {epoch+1}/{epochs}, Batch {batch_idx}, Loss: {loss.item():.4f}')
        
        avg_train_loss = running_loss / len(train_loader)
        train_losses.append(avg_train_loss)
        
        # Testing
        model.eval()
        correct = 0
        total = 0
        with torch.no_grad():
            for data, target in test_loader:
                data, target = data.to(device), target.to(device)
                outputs = model(data)
                _, predicted = torch.max(outputs.data, 1)
                total += target.size(0)
                correct += (predicted == target).sum().item()
        
        accuracy = 100 * correct / total
        test_accuracies.append(accuracy)
        print(f'Epoch {epoch+1}/{epochs} - Loss: {avg_train_loss:.4f}, Accuracy: {accuracy:.2f}%')
    
    return train_losses, test_accuracies

def visualize_flock_trajectories_1_vs_5(model, test_loader, num_samples=1000):
    """Visualize digit classes as flocks of birds navigating hyperspace wind streams"""
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    model.eval()
    
    # Collect data for digit flocks 1 and 5 separately
    flock_1_data = []
    flock_1_activations = []
    flock_5_data = []
    flock_5_activations = []
    
    samples_1_collected = 0
    samples_5_collected = 0
    target_samples = num_samples // 2  # Half for each flock
    
    with torch.no_grad():
        for data, target in test_loader:
            if samples_1_collected >= target_samples and samples_5_collected >= target_samples:
                break
                
            data, target = data.to(device), target.to(device)
            
            # Process pigeon flock (digit 1)
            mask_1 = (target == 1)
            if mask_1.sum() > 0 and samples_1_collected < target_samples:
                pigeon_data = data[mask_1]
                batch_size_1 = min(pigeon_data.size(0), target_samples - samples_1_collected)
                
                activations_1 = model.get_intermediate_activations(pigeon_data[:batch_size_1])
                flock_1_data.append(pigeon_data[:batch_size_1].cpu().numpy())
                
                if not flock_1_activations:
                    flock_1_activations = [[] for _ in range(len(activations_1))]
                
                for i, act in enumerate(activations_1):
                    flock_1_activations[i].append(act)
                
                samples_1_collected += batch_size_1
            
            # Process raven flock (digit 5)
            mask_5 = (target == 5)
            if mask_5.sum() > 0 and samples_5_collected < target_samples:
                raven_data = data[mask_5]
                batch_size_5 = min(raven_data.size(0), target_samples - samples_5_collected)
                
                activations_5 = model.get_intermediate_activations(raven_data[:batch_size_5])
                flock_5_data.append(raven_data[:batch_size_5].cpu().numpy())
                
                if not flock_5_activations:
                    flock_5_activations = [[] for _ in range(len(activations_5))]
                
                for i, act in enumerate(activations_5):
                    flock_5_activations[i].append(act)
                
                samples_5_collected += batch_size_5
    
    # Concatenate flock data
    if not flock_1_data or not flock_5_data:
        print("Could not collect enough birds for both flocks (1s and 5s)")
        return
    
    flock_1_data = np.concatenate(flock_1_data, axis=0)
    flock_5_data = np.concatenate(flock_5_data, axis=0)
    
    for i in range(len(flock_1_activations)):
        flock_1_activations[i] = np.concatenate(flock_1_activations[i], axis=0)
        flock_5_activations[i] = np.concatenate(flock_5_activations[i], axis=0)
    
    print(f"Tracking {len(flock_1_data)} pigeons (1s) and {len(flock_5_data)} ravens (5s) through hyperspace...")
    
    # Create visualization of flocks navigating wind streams
    fig, axes = plt.subplots(2, 3, figsize=(20, 12))
    fig.suptitle('🐦 Flocks Through Hyperspace Wind Streams: Pigeon 1s vs Raven 5s 🌪️', fontsize=16)
    
    # 1. Show flock trajectories through wind layers (ReLU layers)
    wind_layers = [1, 2, 3]  # Wind stream layers
    pigeon_colors = ['lightcoral', 'red', 'darkred']
    raven_colors = ['lightblue', 'blue', 'darkblue']
    
    for plot_idx, wind_layer in enumerate(wind_layers):
        if wind_layer < len(flock_1_activations):
            # Project both flocks to same 2D space to see their paths through this wind layer
            combined_birds = np.vstack([flock_1_activations[wind_layer], 
                                       flock_5_activations[wind_layer]])
            pca = PCA(n_components=2)
            wind_projection = pca.fit_transform(combined_birds)
            
            # Split back to individual flocks
            n_pigeons = len(flock_1_activations[wind_layer])
            pigeon_positions = wind_projection[:n_pigeons]
            raven_positions = wind_projection[n_pigeons:]
            
            # Plot individual birds (light scatter)
            axes[0, plot_idx].scatter(pigeon_positions[:, 0], pigeon_positions[:, 1], 
                                    c=pigeon_colors[0], alpha=0.3, s=8, label='🐦 Pigeons (1s)')
            axes[0, plot_idx].scatter(raven_positions[:, 0], raven_positions[:, 1], 
                                    c=raven_colors[0], alpha=0.3, s=8, label='🐦‍⬛ Ravens (5s)')
            
            # Calculate flock centers and spread
            pigeon_center = np.mean(pigeon_positions, axis=0)
            raven_center = np.mean(raven_positions, axis=0)
            
            # Mark flock centers
            axes[0, plot_idx].scatter(*pigeon_center, c='red', s=200, marker='*', 
                                    edgecolor='black', linewidth=2, label='🐦 Flock Center')
            axes[0, plot_idx].scatter(*raven_center, c='blue', s=200, marker='*', 
                                    edgecolor='black', linewidth=2, label='🐦‍⬛ Flock Center')
            
            axes[0, plot_idx].set_title(f'Wind Layer {wind_layer} 🌪️\n'
                                      f'{flock_1_activations[wind_layer].shape[1]}D Wind Field → 2D View')
            axes[0, plot_idx].set_xlabel('Wind Direction 1')
            axes[0, plot_idx].set_ylabel('Wind Direction 2')
            axes[0, plot_idx].legend(fontsize=8)
            axes[0, plot_idx].grid(True, alpha=0.3)
    
    # 2. Show inter-flock separation (how winds separate the species)
    flock_centers_distance = []
    for layer_activations_1, layer_activations_5 in zip(flock_1_activations[1:], flock_5_activations[1:]):
        # Calculate between-flock separation
        pigeon_center = np.mean(layer_activations_1, axis=0)
        raven_center = np.mean(layer_activations_5, axis=0)
        separation = np.linalg.norm(pigeon_center - raven_center)
        flock_centers_distance.append(separation)
    
    axes[1, 0].plot(range(1, len(flock_centers_distance) + 1), flock_centers_distance, 
                   'o-', linewidth=4, markersize=10, color='purple', 
                   label='🐦 vs 🐦‍⬛ Separation')
    axes[1, 0].fill_between(range(1, len(flock_centers_distance) + 1), flock_centers_distance, 
                          alpha=0.3, color='purple')
    
    axes[1, 0].set_title('Flock Separation Through Wind System 📏\n'
                       'How wind streams guide species to different pigeon holes')
    axes[1, 0].set_xlabel('Wind Layer')
    axes[1, 0].set_ylabel('Distance Between Flock Centers')
    axes[1, 0].set_xticks(range(1, len(flock_centers_distance) + 1))
    axes[1, 0].set_xticklabels([f'Wind {i}' for i in range(1, len(flock_centers_distance) + 1)], rotation=45)
    axes[1, 0].legend()
    axes[1, 0].grid(True, alpha=0.3)
    axes[1, 0].set_yscale('log')
    
    # 3. Show flock cohesion through layers
    layer_cohesions_pigeons = []
    layer_cohesions_ravens = []
    
    for layer_activations_1, layer_activations_5 in zip(flock_1_activations[1:], flock_5_activations[1:]):
        # Calculate within-flock variance (cohesion)
        pigeon_cohesion = np.mean(np.var(layer_activations_1, axis=0))
        raven_cohesion = np.mean(np.var(layer_activations_5, axis=0))
        
        layer_cohesions_pigeons.append(pigeon_cohesion)
        layer_cohesions_ravens.append(raven_cohesion)
    
    wind_layer_names = [f'Wind {i}' for i in range(1, len(layer_cohesions_pigeons) + 1)]
    
    x_pos = np.arange(len(wind_layer_names))
    width = 0.35
    
    axes[1, 1].bar(x_pos - width/2, layer_cohesions_pigeons, width, label='🐦 Pigeon Flock Cohesion', 
           color='red', alpha=0.7)
    axes[1, 1].bar(x_pos + width/2, layer_cohesions_ravens, width, label='🐦‍⬛ Raven Flock Cohesion', 
           color='blue', alpha=0.7)
    
    axes[1, 1].set_title('Flock Cohesion Through Wind Layers 🤝\n'
                 '(Boid rule: Stay together despite wind forces)')
    axes[1, 1].set_xlabel('Wind Layer')
    axes[1, 1].set_ylabel('Within-Flock Variance')
    axes[1, 1].set_xticks(x_pos)
    axes[1, 1].set_xticklabels(wind_layer_names, rotation=45)
    axes[1, 1].legend()
    axes[1, 1].grid(True, alpha=0.3)
    axes[1, 1].set_yscale('log')
    
    # 4. Show dimensionality reduction
    dims = [act.shape[1] for act in flock_1_activations]
    layer_names = ['Input'] + [f'Wind {i}' for i in range(1, len(dims))]
    
    axes[1, 2].plot(range(len(dims)), dims, 'o-', linewidth=2, markersize=8, color='green')
    axes[1, 2].set_title('Dimensionality Through Wind System 📉')
    axes[1, 2].set_xlabel('Layer')
    axes[1, 2].set_ylabel('Dimension')
    axes[1, 2].set_xticks(range(len(layer_names)))
    axes[1, 2].set_xticklabels(layer_names, rotation=45)
    axes[1, 2].grid(True, alpha=0.3)
    axes[1, 2].set_yscale('log')
    
    plt.tight_layout()
    plt.savefig('graphs/flock_trajectories_1_vs_5.png', dpi=300, bbox_inches='tight')
    plt.close()
    
    print("\n" + "="*70)
    print("🐦 FLOCK MIGRATION ANALYSIS: PIGEONS (1s) vs RAVENS (5s) 🐦‍⬛")
    print("="*70)
    print("Observed flock behaviors:")
    print("1. 🌪️  Different species respond uniquely to same wind streams (ReLU layers)")
    print("2. 🤝  Flocks maintain cohesion while navigating through winds (boid rules)")
    print("3. 🛫  Migration paths show how wind system separates species")
    print("4. 📏  Progressive separation guides each flock to correct pigeon hole")
    print("5. 🎯  Wind field engineering creates optimal flight corridors")
    print("="*70)

def create_flock_animation(model, test_loader, num_samples=1000):
    """Create animated GIF showing flocks moving through layers"""
    device = torch.device("cuda" if torch.cuda.is_available() else "cpu")
    model.eval()
    
    # Collect data for digit flocks 1 and 5 separately
    flock_1_data = []
    flock_1_activations = []
    flock_5_data = []
    flock_5_activations = []
    
    samples_1_collected = 0
    samples_5_collected = 0
    target_samples = num_samples // 2  # Half for each flock
    
    with torch.no_grad():
        for data, target in test_loader:
            if samples_1_collected >= target_samples and samples_5_collected >= target_samples:
                break
                
            data, target = data.to(device), target.to(device)
            
            # Process pigeon flock (digit 1)
            mask_1 = (target == 1)
            if mask_1.sum() > 0 and samples_1_collected < target_samples:
                pigeon_data = data[mask_1]
                batch_size_1 = min(pigeon_data.size(0), target_samples - samples_1_collected)
                
                activations_1 = model.get_intermediate_activations(pigeon_data[:batch_size_1])
                flock_1_data.append(pigeon_data[:batch_size_1].cpu().numpy())
                
                if not flock_1_activations:
                    flock_1_activations = [[] for _ in range(len(activations_1))]
                
                for i, act in enumerate(activations_1):
                    flock_1_activations[i].append(act)
                
                samples_1_collected += batch_size_1
            
            # Process raven flock (digit 5)
            mask_5 = (target == 5)
            if mask_5.sum() > 0 and samples_5_collected < target_samples:
                raven_data = data[mask_5]
                batch_size_5 = min(raven_data.size(0), target_samples - samples_5_collected)
                
                activations_5 = model.get_intermediate_activations(raven_data[:batch_size_5])
                flock_5_data.append(raven_data[:batch_size_5].cpu().numpy())
                
                if not flock_5_activations:
                    flock_5_activations = [[] for _ in range(len(activations_5))]
                
                for i, act in enumerate(activations_5):
                    flock_5_activations[i].append(act)
                
                samples_5_collected += batch_size_5
    
    # Concatenate flock data
    if not flock_1_data or not flock_5_data:
        print("Could not collect enough birds for both flocks (1s and 5s)")
        return
    
    flock_1_data = np.concatenate(flock_1_data, axis=0)
    flock_5_data = np.concatenate(flock_5_data, axis=0)
    
    for i in range(len(flock_1_activations)):
        flock_1_activations[i] = np.concatenate(flock_1_activations[i], axis=0)
        flock_5_activations[i] = np.concatenate(flock_5_activations[i], axis=0)
    
    print(f"Creating animation of {len(flock_1_data)} pigeons (1s) and {len(flock_5_data)} ravens (5s)...")
    
    # Pre-compute all projections for consistent scaling across frames
    all_projections_1 = []
    all_projections_5 = []
    global_min_x, global_max_x = float('inf'), float('-inf')
    global_min_y, global_max_y = float('inf'), float('-inf')
    
    for layer_idx in range(1, len(flock_1_activations)):  # Skip input layer
        combined_birds = np.vstack([flock_1_activations[layer_idx], flock_5_activations[layer_idx]])
        pca = PCA(n_components=2)
        wind_projection = pca.fit_transform(combined_birds)
        
        n_pigeons = len(flock_1_activations[layer_idx])
        pigeon_positions = wind_projection[:n_pigeons]
        raven_positions = wind_projection[n_pigeons:]
        
        all_projections_1.append(pigeon_positions)
        all_projections_5.append(raven_positions)
        
        # Update global bounds for consistent scaling
        all_positions = np.vstack([pigeon_positions, raven_positions])
        global_min_x = min(global_min_x, all_positions[:, 0].min())
        global_max_x = max(global_max_x, all_positions[:, 0].max())
        global_min_y = min(global_min_y, all_positions[:, 1].min())
        global_max_y = max(global_max_y, all_positions[:, 1].max())
    
    # Add padding to bounds
    padding = 0.1 * max(global_max_x - global_min_x, global_max_y - global_min_y)
    global_min_x -= padding
    global_max_x += padding
    global_min_y -= padding
    global_max_y += padding
    
    # Create animation
    fig, ax = plt.subplots(1, 1, figsize=(12, 10))
    
    def animate(frame):
        ax.clear()
        
        if frame < len(all_projections_1):
            pigeon_positions = all_projections_1[frame]
            raven_positions = all_projections_5[frame]
            
            # Plot individual birds with trails (fade effect)
            trail_length = min(3, frame + 1)
            for trail_frame in range(max(0, frame - trail_length + 1), frame + 1):
                if trail_frame < len(all_projections_1):
                    alpha = 0.1 + 0.7 * (trail_frame - max(0, frame - trail_length + 1)) / max(1, trail_length - 1)
                    size = 3 + 15 * (trail_frame - max(0, frame - trail_length + 1)) / max(1, trail_length - 1)
                    
                    trail_pigeon_pos = all_projections_1[trail_frame]
                    trail_raven_pos = all_projections_5[trail_frame]
                    
                    ax.scatter(trail_pigeon_pos[:, 0], trail_pigeon_pos[:, 1], 
                             c='red', alpha=alpha, s=size, label='Pigeons (1s)' if trail_frame == frame else "")
                    ax.scatter(trail_raven_pos[:, 0], trail_raven_pos[:, 1], 
                             c='blue', alpha=alpha, s=size, label='Ravens (5s)' if trail_frame == frame else "")
            
            # Calculate and show flock centers
            pigeon_center = np.mean(pigeon_positions, axis=0)
            raven_center = np.mean(raven_positions, axis=0)
            
            # Draw connection between centers
            ax.plot([pigeon_center[0], raven_center[0]], [pigeon_center[1], raven_center[1]], 
                   'purple', linewidth=3, alpha=0.5, linestyle='--', 
                   label=f'Separation: {np.linalg.norm(pigeon_center - raven_center):.1f}')
            
            # Mark flock centers
            ax.scatter(*pigeon_center, c='darkred', s=300, marker='*', 
                      edgecolor='white', linewidth=3, label='Pigeon Flock Center', zorder=10)
            ax.scatter(*raven_center, c='darkblue', s=300, marker='*', 
                      edgecolor='white', linewidth=3, label='Raven Flock Center', zorder=10)
            
            # Add wind field visualization
            x_range = np.linspace(global_min_x, global_max_x, 8)
            y_range = np.linspace(global_min_y, global_max_y, 6)
            X, Y = np.meshgrid(x_range, y_range)
            
            # Create "wind vectors" that change with layer
            wind_strength = 0.3 * (frame + 1) / len(all_projections_1)
            U = wind_strength * (X - np.mean(X)) * np.sin(frame * 0.5)
            V = wind_strength * (Y - np.mean(Y)) * np.cos(frame * 0.5)
            
            ax.quiver(X, Y, U, V, alpha=0.3, color='gray', scale=8)
            
            layer_num = frame + 1
            dimensions = flock_1_activations[layer_num].shape[1] if layer_num < len(flock_1_activations) else 'Output'
            
            ax.set_title(f'Wind Layer {layer_num}: Flocks Through {dimensions}D Space\n'
                        f'Frame {frame + 1}/{len(all_projections_1)} - Watch the migration!', 
                        fontsize=14, pad=20)
        
        ax.set_xlim(global_min_x, global_max_x)
        ax.set_ylim(global_min_y, global_max_y)
        ax.set_xlabel('Wind Direction 1', fontsize=12)
        ax.set_ylabel('Wind Direction 2', fontsize=12)
        ax.grid(True, alpha=0.3)
        ax.legend(loc='upper right', fontsize=10)
        
        # Add progress bar
        progress = (frame + 1) / len(all_projections_1)
        progress_bar_width = 0.8 * (global_max_x - global_min_x)
        progress_bar_x = global_min_x + 0.1 * (global_max_x - global_min_x)
        progress_bar_y = global_min_y + 0.05 * (global_max_y - global_min_y)
        
        # Progress bar background
        ax.barh(progress_bar_y, progress_bar_width, height=0.02 * (global_max_y - global_min_y), 
               left=progress_bar_x, color='lightgray', alpha=0.5, zorder=0)
        # Progress bar fill
        ax.barh(progress_bar_y, progress * progress_bar_width, height=0.02 * (global_max_y - global_min_y),
               left=progress_bar_x, color='green', alpha=0.8, zorder=1)
    
    # Create animation
    anim = animation.FuncAnimation(fig, animate, frames=len(all_projections_1), 
                                 interval=800, repeat=True, blit=False)
    
    # Save as GIF
    print("Saving animation as GIF (this may take a moment)...")
    anim.save('graphs/flock_migration.gif', writer='pillow', fps=1.2, dpi=100)
    plt.close()
    
    print("\n" + "="*70)
    print("🎬 FLOCK MIGRATION ANIMATION CREATED! 🎬")
    print("="*70)
    print("Animation saved as: graphs/flock_migration.gif")
    print("Watch how:")
    print("1. 🐦 Pigeon and raven flocks move through wind layers")
    print("2. 🌪️ Wind fields change and guide the flocks")
    print("3. 📏 Separation distance evolves through the network")
    print("4. 🎯 Each flock finds its way to the correct destination")
    print("5. 👻 Flock trails show the migration path history")
    print("="*70)

def main():
    """Main function to run the complete analysis"""
    print("="*60)
    print("MNIST SNAKE ANALYSIS: Finding the Squiggle in ReLU Networks")
    print("="*60)
    
    # Load data
    train_loader, test_loader = load_mnist_data()
    
    # Create model
    model = SnakeNet(
        input_size=784,
        hidden_sizes=[512, 256, 128, 64],  # Progressively smaller
        num_classes=10
    )
    
    print(f"Created network with architecture: {model.layer_dims}")
    print(f"Total parameters: {sum(p.numel() for p in model.parameters()):,}")
    
    # Train model
    train_losses, test_accuracies = train_model(model, train_loader, test_loader, epochs=3)
    
    print(f"\nFinal accuracy: {test_accuracies[-1]:.2f}%")
    
    # Visualize flocks navigating through hyperspace wind streams
    print("\nTracking flocks of 1s (pigeons) and 5s (ravens) through hyperspace wind streams...")
    visualize_flock_trajectories_1_vs_5(model, test_loader, num_samples=2000)
    
    # Create animated visualization
    print("\nCreating animated migration visualization...")
    create_flock_animation(model, test_loader, num_samples=1000)
    
    print("\n" + "="*60)
    print("Analysis complete! Generated files in graphs/:")
    print("1. flock_trajectories_1_vs_5.png - Shows pigeon vs raven flocks through wind streams")
    print("2. flock_migration.gif - Animated migration through all layers!")
    print("="*60)
    print("Look for:")
    print("1. 🐦 Different flock behavior patterns for pigeons (1s) vs ravens (5s)")
    print("2. 🌪️ How wind streams (ReLU layers) guide flocks differently") 
    print("3. 🤝 Flock cohesion maintained through turbulent wind fields")
    print("4. 🛫 Migration paths showing species separation through wind system")
    print("5. 🎯 Final approach to correct pigeon holes via engineered wind corridors")
    print("6. 🎬 Watch the full migration journey in the animated GIF!")
    print("="*60)

if __name__ == "__main__":
    main()