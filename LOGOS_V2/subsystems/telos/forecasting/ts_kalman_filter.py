"""
Forecasting Toolkit: Time Series Kalman
Scaffold + operational code
"""
import numpy as np
from pykalman import KalmanFilter as PKKalmanFilter

class TimeSeriesKalman:
    """
    Wrapper around pykalman's KalmanFilter for time-series smoothing.
    """
    def __init__(self, transition_matrices=None, observation_matrices=None,
                 transition_covariance=None, observation_covariance=None,
                 initial_state_mean=None, initial_state_covariance=None):

        self.kf = PKKalmanFilter(
            transition_matrices=transition_matrices,
            observation_matrices=observation_matrices,
            transition_covariance=transition_covariance,
            observation_covariance=observation_covariance,
            initial_state_mean=initial_state_mean,
            initial_state_covariance=initial_state_covariance
        )

    def fit(self, observations):
        """
        Fit the Kalman filter to observations.
        Returns state means and covariances.
        """
        state_means, state_covariances = self.kf.filter(observations)
        return state_means, state_covariances

    def predict(self, n_steps, current_state=None):
        """
        Predict the next `n_steps` states.
        """
        if current_state is None:
            current_state = self.kf.initial_state_mean

        predictions = []
        for _ in range(n_steps):
            current_state = self.kf.transition_matrices.dot(current_state)
            predictions.append(current_state)
        return np.array(predictions)
