import numpy as np
import plotly.graph_objects as go

# Parameters
max_iter = 25
bound = 2.0
grid_size = 50  # Resolution
c = 0.01 + 0.01j  # Small complex constant for variation

# Create 3D grid
x = np.linspace(-1.5, 1.5, grid_size)
y = np.linspace(-1.5, 1.5, grid_size)
z = np.linspace(-1.5, 1.5, grid_size)
X, Y, Z = np.meshgrid(x, y, z)

# Initialize arrays for iteration
V = X + 1j*Y + Z
escape_mask = np.zeros(V.shape, dtype=bool)
colors = np.empty(V.shape, dtype=object)

# Axis colors for bounded points
axis_colors = { 'X': 'orange', 'Y': 'purple', 'Z': 'green' }

# Function to determine escape color
def escape_color(x, y, z):
    abs_vals = np.array([abs(x), abs(y), abs(z)])
    max_idx = np.argmax(abs_vals)
    if max_idx == 0:
        return 'red'      # X escape
    elif max_idx == 1:
        return 'blue'     # Y escape
    else:
        return 'yellow'   # Z escape

# Iterate fractal formula
for i in range(max_iter):
    norm = np.abs(V)
    escaped = norm > bound
    # Color escapes based on axis
    colors[escaped & ~escape_mask] = [escape_color(xv, yv, zv) for xv, yv, zv in zip(X[escaped & ~escape_mask].flat, 
                                                                                   Y[escaped & ~escape_mask].flat, 
                                                                                   Z[escaped & ~escape_mask].flat)]
    escape_mask |= escaped
    # Update fractal (trinitarian-inspired)
    V = (V**3 + V**2 + V + c)

# Assign bounded core colors (where not escaped)
colors[~escape_mask] = [axis_colors['X'] if abs(xv) >= abs(yv) and abs(xv) >= abs(zv)
                        else axis_colors['Y'] if abs(yv) >= abs(zv)
                        else axis_colors['Z'] 
                        for xv, yv, zv in zip(X[~escape_mask].flat, Y[~escape_mask].flat, Z[~escape_mask].flat)]

# Flatten for plotting
X_flat = X.flatten()
Y_flat = Y.flatten()
Z_flat = Z.flatten()
colors_flat = colors.flatten()

# Create 3D scatter plot
fig = go.Figure(data=[go.Scatter3d(
    x=X_flat,
    y=Y_flat,
    z=Z_flat,
    mode='markers',
    marker=dict(
        size=3,
        color=colors_flat,
        opacity=0.7
    )
)])

fig.update_layout(
    scene=dict(
        xaxis_title='Spirit (X)',
        yaxis_title='Son (Y)',
        zaxis_title='Father (Z)',
    ),
    title='Trinitarian-Inspired 3D Fractal',
    width=800,
    height=800
)

fig.show()
