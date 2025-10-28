"""
Forecasting Toolkit: State Space Model Builder
Scaffold + operational code
"""
import numpy as np

def build_state_space_model(n, process_var=1e-5, measurement_var=1e-1):
    """
    Construct basic state-space matrices for dimension `n`.
    """
    A = np.eye(n)
    B = np.eye(n)
    H = np.eye(n)
    Q = process_var * np.eye(n)
    R = measurement_var * np.eye(n)
    x0 = np.zeros((n, 1))
    P0 = np.eye(n)
    return A, B, H, Q, R, x0, P0
