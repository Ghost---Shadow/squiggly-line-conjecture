import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import FancyArrowPatch
from matplotlib.animation import FuncAnimation
import os

# Create output directory
os.makedirs("graphs", exist_ok=True)

def create_wind_tunnel_static():
    """Create a static wind tunnel visualization with tapering arrows"""
    
    fig, ax = plt.subplots(figsize=(14, 8))
    
    # Set up the wind tunnel box
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 5)
    ax.set_aspect('equal')
    
    # Draw tunnel walls
    ax.plot([0, 10], [0, 0], 'k-', linewidth=3)  # Bottom wall
    ax.plot([0, 10], [5, 5], 'k-', linewidth=3)  # Top wall
    ax.plot([0, 0], [0, 5], 'k-', linewidth=3)    # Left wall
    ax.plot([10, 10], [0, 5], 'k-', linewidth=3)  # Right wall
    
    # Create grid of arrows
    n_rows = 8
    n_cols = 12
    
    # Generate positions
    x_positions = np.linspace(0.5, 9.5, n_cols)
    y_positions = np.linspace(0.5, 4.5, n_rows)
    
    for i, x in enumerate(x_positions):
        for j, y in enumerate(y_positions):
            # Calculate taper factor (stronger taper near the end)
            taper_factor = 1.0 - (x / 10) ** 2 * 0.7
            
            # Arrow properties that change with position
            arrow_length = 0.6 * taper_factor
            arrow_width = 0.02 * taper_factor
            head_width = 0.15 * taper_factor
            head_length = 0.1 * taper_factor
            
            # Vary alpha to create depth effect
            alpha = 0.3 + 0.4 * taper_factor
            
            # Add some randomness to make it more natural
            y_offset = np.sin(x * 2 + j * 0.5) * 0.1 * taper_factor
            
            # Draw arrow
            arrow = FancyArrowPatch(
                (x - arrow_length/2, y + y_offset),
                (x + arrow_length/2, y + y_offset),
                arrowstyle='->,head_width=' + str(head_width) + ',head_length=' + str(head_length),
                color='gray',
                alpha=alpha,
                linewidth=1.5 * taper_factor,
                zorder=1
            )
            ax.add_patch(arrow)
    
    # Add title and labels
    ax.set_title('Wind Tunnel Visualization', fontsize=16, fontweight='bold')
    ax.set_xlabel('Distance →', fontsize=12)
    ax.set_ylabel('Height', fontsize=12)
    
    # Remove ticks for cleaner look
    ax.set_xticks([])
    ax.set_yticks([])
    
    # Add inlet and outlet labels
    ax.text(0.2, 2.5, 'INLET', fontsize=14, fontweight='bold', 
            rotation=90, va='center', ha='center')
    ax.text(9.8, 2.5, 'OUTLET', fontsize=14, fontweight='bold', 
            rotation=90, va='center', ha='center')
    
    plt.tight_layout()
    plt.savefig('graphs/wind_tunnel_static.png', dpi=300, bbox_inches='tight')
    plt.close()
    
    print("Static wind tunnel saved to: graphs/wind_tunnel_static.png")


def create_wind_tunnel_animated():
    """Create an animated wind tunnel with flowing arrows"""
    
    fig, ax = plt.subplots(figsize=(14, 8))
    
    # Set up the wind tunnel box
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 5)
    ax.set_aspect('equal')
    
    # Draw tunnel walls (persistent)
    ax.plot([0, 10], [0, 0], 'k-', linewidth=3)  # Bottom wall
    ax.plot([0, 10], [5, 5], 'k-', linewidth=3)  # Top wall
    ax.plot([0, 0], [0, 5], 'k-', linewidth=3)    # Left wall
    ax.plot([10, 10], [0, 5], 'k-', linewidth=3)  # Right wall
    
    # Add labels (persistent)
    ax.set_title('Wind Tunnel Animation', fontsize=16, fontweight='bold')
    ax.set_xlabel('Distance →', fontsize=12)
    ax.set_ylabel('Height', fontsize=12)
    ax.set_xticks([])
    ax.set_yticks([])
    ax.text(0.2, 2.5, 'INLET', fontsize=14, fontweight='bold', 
            rotation=90, va='center', ha='center')
    ax.text(9.8, 2.5, 'OUTLET', fontsize=14, fontweight='bold', 
            rotation=90, va='center', ha='center')
    
    # Storage for arrow patches
    arrows = []
    
    def init():
        return arrows
    
    def animate(frame):
        # Clear previous arrows
        for arrow in arrows:
            arrow.remove()
        arrows.clear()
        
        # Create grid of arrows with phase shift for animation
        n_rows = 8
        n_cols = 12
        
        # Generate positions
        x_positions = np.linspace(0.5, 9.5, n_cols)
        y_positions = np.linspace(0.5, 4.5, n_rows)
        
        # Phase shift for animation
        phase = frame * 0.1
        
        for i, x in enumerate(x_positions):
            for j, y in enumerate(y_positions):
                # Animated x position
                x_animated = x + np.sin(phase + i * 0.3) * 0.15
                
                # Calculate taper factor
                taper_factor = 1.0 - (x / 10) ** 2 * 0.7
                
                # Arrow properties
                arrow_length = 0.6 * taper_factor
                arrow_width = 0.02 * taper_factor
                head_width = 0.15 * taper_factor
                head_length = 0.1 * taper_factor
                
                # Vary alpha
                alpha = 0.3 + 0.4 * taper_factor
                
                # Add wave motion
                y_offset = np.sin(x * 2 + j * 0.5 + phase) * 0.1 * taper_factor
                
                # Create arrow
                arrow = FancyArrowPatch(
                    (x_animated - arrow_length/2, y + y_offset),
                    (x_animated + arrow_length/2, y + y_offset),
                    arrowstyle='->,head_width=' + str(head_width) + ',head_length=' + str(head_length),
                    color='gray',
                    alpha=alpha,
                    linewidth=1.5 * taper_factor,
                    zorder=1
                )
                ax.add_patch(arrow)
                arrows.append(arrow)
        
        return arrows
    
    # Create animation
    anim = FuncAnimation(fig, animate, init_func=init, frames=60, 
                        interval=50, blit=True, repeat=True)
    
    # Save as GIF
    anim.save('graphs/wind_tunnel_animated.gif', writer='pillow', fps=20, dpi=100)
    plt.close()
    
    print("Animated wind tunnel saved to: graphs/wind_tunnel_animated.gif")


def create_3d_wind_tunnel():
    """Create a 3D wind tunnel visualization"""
    from mpl_toolkits.mplot3d import Axes3D
    
    fig = plt.figure(figsize=(14, 10))
    ax = fig.add_subplot(111, projection='3d')
    
    # Set up the 3D space
    ax.set_xlim(0, 10)
    ax.set_ylim(0, 5)
    ax.set_zlim(0, 5)
    
    # Draw tunnel frame
    # Bottom rectangle
    x_corners = [0, 10, 10, 0, 0]
    y_corners = [0, 0, 5, 5, 0]
    z_corners = [0, 0, 0, 0, 0]
    ax.plot(x_corners, y_corners, z_corners, 'k-', linewidth=2)
    
    # Top rectangle
    z_top = [5, 5, 5, 5, 5]
    ax.plot(x_corners, y_corners, z_top, 'k-', linewidth=2)
    
    # Vertical edges
    for i in range(4):
        ax.plot([x_corners[i], x_corners[i]], 
                [y_corners[i], y_corners[i]], 
                [0, 5], 'k-', linewidth=2)
    
    # Create 3D grid of arrows
    n_x = 10
    n_y = 6
    n_z = 6
    
    x_positions = np.linspace(0.5, 9.5, n_x)
    y_positions = np.linspace(0.5, 4.5, n_y)
    z_positions = np.linspace(0.5, 4.5, n_z)
    
    for i, x in enumerate(x_positions):
        for j, y in enumerate(y_positions):
            for k, z in enumerate(z_positions):
                # Calculate taper factor
                taper_factor = 1.0 - (x / 10) ** 2 * 0.7
                
                # Arrow properties
                arrow_length = 0.8 * taper_factor
                
                # Vary alpha for depth
                alpha = 0.2 + 0.3 * taper_factor
                
                # Draw arrow as a line with quiver
                ax.quiver(x - arrow_length/2, y, z,
                         arrow_length, 0, 0,
                         color='gray', alpha=alpha,
                         arrow_length_ratio=0.2 * taper_factor,
                         linewidth=1 * taper_factor)
    
    # Set labels
    ax.set_xlabel('Flow Direction →', fontsize=12)
    ax.set_ylabel('Width', fontsize=12)
    ax.set_zlabel('Height', fontsize=12)
    ax.set_title('3D Wind Tunnel Visualization', fontsize=16, fontweight='bold')
    
    # Set viewing angle
    ax.view_init(elev=20, azim=-60)
    
    plt.tight_layout()
    plt.savefig('graphs/wind_tunnel_3d.png', dpi=300, bbox_inches='tight')
    plt.close()
    
    print("3D wind tunnel saved to: graphs/wind_tunnel_3d.png")


def main():
    """Main function to create all wind tunnel visualizations"""
    print("=" * 60)
    print("WIND TUNNEL VISUALIZATION")
    print("=" * 60)
    
    print("\nCreating static wind tunnel...")
    create_wind_tunnel_static()
    
    print("\nCreating animated wind tunnel...")
    create_wind_tunnel_animated()
    
    print("\nCreating 3D wind tunnel...")
    create_3d_wind_tunnel()
    
    print("\n" + "=" * 60)
    print("All visualizations complete!")
    print("Generated files:")
    print("1. graphs/wind_tunnel_static.png - Static view with tapering arrows")
    print("2. graphs/wind_tunnel_animated.gif - Animated flowing arrows")
    print("3. graphs/wind_tunnel_3d.png - 3D perspective view")
    print("=" * 60)


if __name__ == "__main__":
    main()