# logos_agi_v1/subsystems/telos/__init__.py

"""
TELOS - The Scientist

Scientific reasoning, causal inference, and outcome prediction subsystem
for the LOGOS AGI architecture.

Capabilities:
- Structural causal modeling and inference
- Outcome prediction and forecasting
- Causal retrodiction (inferring causes from effects)
- Intervention analysis and planning
- Time series analysis and forecasting
- Scientific hypothesis testing
- Counterfactual reasoning

This subsystem provides the empirical and scientific reasoning capabilities
needed for understanding cause-and-effect relationships in complex systems.
"""

__version__ = "1.0.0"
__author__ = "LOGOS AGI Development Team"
__subsystem__ = "TELOS"

from .telos_worker import TelosWorker, TelosCoreEngine

__all__ = [
    "TelosWorker",
    "TelosCoreEngine"
]

# Subsystem metadata
SUBSYSTEM_INFO = {
    "name": "TELOS",
    "version": __version__,
    "description": "Scientific Reasoning and Causal Inference",
    "capabilities": [
        "causal_modeling",
        "outcome_prediction",
        "causal_retrodiction", 
        "intervention_analysis",
        "time_series_forecasting",
        "hypothesis_testing",
        "counterfactual_reasoning"
    ],
    "input_queues": ["telos_task_queue"],
    "output_queues": ["task_result_queue"],
    "dependencies": [
        "scikit-learn",
        "causal-learn",
        "scipy",
        "numpy",
        "statsmodels"
    ]
}