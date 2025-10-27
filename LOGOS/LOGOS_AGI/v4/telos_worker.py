# logos_agi_v1/subsystems/telos/telos_worker.py

"""
TELOS Scientific Reasoning Worker

The Scientist - handles causal reasoning, outcome prediction, retrodiction,
and scientific hypothesis testing using structural causal models.

Responsibilities:
- Causal inference and intervention analysis
- Outcome prediction and forecasting
- Causal retrodiction (inferring causes from effects)
- Counterfactual reasoning
- Scientific hypothesis validation
- Time series analysis and forecasting
"""

import os
import sys
import json
import time
import logging
import signal
import uuid
from typing import Dict, List, Any, Optional, Tuple
from datetime import datetime
from collections import defaultdict

# RabbitMQ and messaging
import pika

# Core LOGOS imports
try:
    from core.causal.scm import SCM
    from core.causal.counterfactuals import evaluate_counterfactual
    from core.causal.planner import Planner
    from core.data_structures import TaskDescriptor, OperationResult
except ImportError:
    # Fallback implementations if core modules aren't available
    pass

# Scientific computing libraries with fallbacks
try:
    import numpy as np
    import pandas as pd
    from scipy import stats
    from sklearn.linear_model import LinearRegression
    from sklearn.ensemble import RandomForestRegressor

    NUMPY_AVAILABLE = True
    PANDAS_AVAILABLE = True
    SCIPY_AVAILABLE = True
    SKLEARN_AVAILABLE = True
except ImportError:
    NUMPY_AVAILABLE = False
    PANDAS_AVAILABLE = False
    SCIPY_AVAILABLE = False
    SKLEARN_AVAILABLE = False

# Configuration
SUBSYSTEM_NAME = "TELOS"
RABBITMQ_HOST = os.getenv("RABBITMQ_HOST", "rabbitmq")
RABBITMQ_PORT = int(os.getenv("RABBITMQ_PORT", "5672"))
TASK_QUEUE = "telos_task_queue"
RESULT_QUEUE = "task_result_queue"

# Logging setup
logging.basicConfig(
    level=logging.INFO,
    format=f"%(asctime)s - %(levelname)s - {SUBSYSTEM_NAME}_WORKER - %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler("/app/logs/telos_worker.log", mode="a"),
    ],
)


class SCMImplementation:
    """
    Structural Causal Model implementation for causal reasoning.
    Provides causal inference, intervention analysis, and counterfactual reasoning.
    """

    def __init__(self, dag=None):
        self.dag = dag or {}  # Directed Acyclic Graph representing causal structure
        self.parameters = {}  # Learned parameters for each node
        self.interventions = {}  # Active interventions

    def fit(self, data: List[Dict[str, Any]]) -> bool:
        """
        Fit the structural equations to observational data.
        Learn conditional probability distributions for each variable.
        """
        try:
            if not data:
                return False

            # Build conditional probability tables
            counts = {}
            for node, parents in self.dag.items():
                counts[node] = defaultdict(lambda: defaultdict(int))

                for sample in data:
                    if all(p in sample for p in parents) and node in sample:
                        # Create parent configuration key
                        parent_key = tuple(sample.get(p) for p in parents) if parents else ()
                        node_value = sample.get(node)

                        if node_value is not None:
                            counts[node][parent_key][node_value] += 1

            # Convert counts to probabilities
            self.parameters = {}
            for node, parent_configs in counts.items():
                self.parameters[node] = {}
                for parent_key, value_counts in parent_configs.items():
                    total = sum(value_counts.values())
                    if total > 0:
                        self.parameters[node][parent_key] = {
                            value: count / total for value, count in value_counts.items()
                        }

            return True

        except Exception as e:
            logging.error(f"SCM fitting failed: {e}")
            return False

    def do(self, intervention: Dict[str, Any]):
        """
        Create a new SCM with the specified intervention (do-calculus).
        Returns a new SCM instance with the intervention applied.
        """
        new_scm = SCMImplementation(dag=self.dag.copy())
        new_scm.parameters = self.parameters.copy()
        new_scm.interventions = {**self.interventions, **intervention}
        return new_scm

    def counterfactual(self, query: Dict[str, Any]) -> float:
        """
        Evaluate a counterfactual query: P(target | do(intervention), context).
        """
        target = query.get("target")
        intervention = query.get("do", {})
        context = query.get("context", {})

        # Simple counterfactual evaluation
        if target in intervention:
            return 1.0  # If we directly intervene on target, probability is 1

        # Get parameters for the target variable
        target_params = self.parameters.get(target, {})
        if not target_params:
            return 0.5  # Default probability if no learned parameters

        # Find relevant parent configuration
        parents = self.dag.get(target, [])
        parent_config = tuple(context.get(p, intervention.get(p)) for p in parents)

        # Get probability distribution for this configuration
        prob_dist = target_params.get(parent_config, {})
        if not prob_dist:
            return 0.5  # Default if configuration not seen in training

        # Return probability of the most likely outcome
        return max(prob_dist.values()) if prob_dist else 0.5

    def predict_intervention_effect(
        self, intervention: Dict[str, Any], target_variables: List[str]
    ) -> Dict[str, float]:
        """
        Predict the effect of an intervention on target variables.
        """
        effects = {}
        intervened_scm = self.do(intervention)

        for target in target_variables:
            # Simulate effect by evaluating counterfactual
            effect = intervened_scm.counterfactual(
                {"target": target, "do": intervention, "context": {}}
            )
            effects[target] = effect

        return effects


class TelosCoreEngine:
    """
    Core logic engine for TELOS subsystem.
    Encapsulates causal reasoning, prediction, and scientific analysis.
    """

    def __init__(self):
        self.logger = logging.getLogger("TELOS_CORE")
        self.worker_id = f"telos_{uuid.uuid4().hex[:8]}"

        # Initialize causal reasoning components
        self.scm_models = {}  # Store multiple SCM models
        self.prediction_cache = {}
        self.forecasting_models = {}

        # Initialize scientific analysis tools
        self._initialize_analysis_tools()

        self.logger.info(f"TELOS Core Engine initialized with worker ID: {self.worker_id}")

    def _initialize_analysis_tools(self):
        """Initialize scientific analysis and forecasting tools."""
        try:
            if SKLEARN_AVAILABLE:
                self.linear_predictor = LinearRegression()
                self.rf_predictor = RandomForestRegressor(n_estimators=50, random_state=42)
                self.logger.info("Scikit-learn predictors initialized")

            # Initialize simple forecasting models
            self.forecasting_methods = ["linear_trend", "moving_average", "exponential_smoothing"]

        except Exception as e:
            self.logger.warning(f"Analysis tools initialization failed: {e}")

    def execute(self, task_type: str, payload: Dict[str, Any]) -> Dict[str, Any]:
        """
        Main execution entry point for TELOS tasks.
        Routes tasks to appropriate scientific reasoning methods.
        """
        try:
            self.logger.info(f"Executing task type: {task_type}")

            if task_type == "predict_outcomes":
                return self._predict_outcomes(payload)
            elif task_type == "causal_retrodiction":
                return self._causal_retrodiction(payload)
            elif task_type == "analyze_intervention":
                return self._analyze_intervention(payload)
            elif task_type == "forecast_series":
                return self._forecast_time_series(payload)
            elif task_type == "test_hypothesis":
                return self._test_hypothesis(payload)
            elif task_type == "build_causal_model":
                return self._build_causal_model(payload)
            else:
                return {
                    "status": "error",
                    "error": f"Unknown task type: {task_type}",
                    "supported_tasks": [
                        "predict_outcomes",
                        "causal_retrodiction",
                        "analyze_intervention",
                        "forecast_series",
                        "test_hypothesis",
                        "build_causal_model",
                    ],
                }

        except Exception as e:
            self.logger.error(f"Error executing task {task_type}: {e}", exc_info=True)
            return {"status": "error", "error": str(e), "task_type": task_type}

    def _predict_outcomes(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Predict outcomes based on current state and interventions."""
        try:
            current_state = payload.get("current_state", {})
            interventions = payload.get("interventions", [])
            target_variables = payload.get("target_variables", [])
            prediction_horizon = payload.get("horizon", 1)

            predictions = {}
            confidence_scores = {}

            for intervention in interventions:
                intervention_id = intervention.get("id", f"intervention_{len(predictions)}")
                intervention_params = intervention.get("parameters", {})

                # Use SCM if available and trained
                if hasattr(self, "scm_models") and "default" in self.scm_models:
                    scm = self.scm_models["default"]
                    effects = scm.predict_intervention_effect(intervention_params, target_variables)

                    predictions[intervention_id] = {
                        "intervention": intervention_params,
                        "predicted_effects": effects,
                        "method": "structural_causal_model",
                    }
                    confidence_scores[intervention_id] = 0.8

                else:
                    # Fallback prediction using simple heuristics
                    predicted_effects = {}
                    for target in target_variables:
                        if target in intervention_params:
                            # Direct intervention effect
                            predicted_effects[target] = intervention_params[target]
                        elif target in current_state:
                            # Assume some correlation with current state
                            base_value = current_state[target]
                            intervention_strength = sum(
                                abs(v)
                                for v in intervention_params.values()
                                if isinstance(v, (int, float))
                            )
                            predicted_effects[target] = base_value * (
                                1 + intervention_strength * 0.1
                            )
                        else:
                            # Default prediction
                            predicted_effects[target] = 0.5

                    predictions[intervention_id] = {
                        "intervention": intervention_params,
                        "predicted_effects": predicted_effects,
                        "method": "heuristic_prediction",
                    }
                    confidence_scores[intervention_id] = 0.6

            return {
                "status": "success",
                "predictions": predictions,
                "confidence_scores": confidence_scores,
                "prediction_horizon": prediction_horizon,
                "target_variables": target_variables,
                "total_interventions_analyzed": len(interventions),
            }

        except Exception as e:
            return {"status": "error", "error": f"Outcome prediction failed: {str(e)}"}

    def _causal_retrodiction(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Infer likely causes from observed effects (retrodiction)."""
        try:
            observed_effects = payload.get("observed_effects", {})
            possible_causes = payload.get("possible_causes", [])
            context = payload.get("context", {})

            cause_likelihoods = {}

            for cause in possible_causes:
                cause_id = cause.get("id", str(cause))
                cause_params = cause.get("parameters", cause if isinstance(cause, dict) else {})

                # Calculate likelihood that this cause produced the observed effects
                likelihood = 0.0
                explanation_quality = 0.0

                for effect_var, effect_value in observed_effects.items():
                    # Simple heuristic: if cause directly affects the variable
                    if effect_var in cause_params:
                        if isinstance(effect_value, (int, float)) and isinstance(
                            cause_params[effect_var], (int, float)
                        ):
                            # Numeric comparison
                            difference = abs(effect_value - cause_params[effect_var])
                            var_likelihood = max(0, 1 - difference)
                        else:
                            # Categorical comparison
                            var_likelihood = (
                                1.0 if effect_value == cause_params[effect_var] else 0.0
                            )
                    else:
                        # Indirect effect estimation
                        var_likelihood = 0.3  # Default weak connection

                    likelihood += var_likelihood
                    explanation_quality += var_likelihood

                # Normalize by number of effects
                if len(observed_effects) > 0:
                    likelihood /= len(observed_effects)
                    explanation_quality /= len(observed_effects)

                cause_likelihoods[cause_id] = {
                    "likelihood": likelihood,
                    "explanation_quality": explanation_quality,
                    "cause_parameters": cause_params,
                }

            # Rank causes by likelihood
            ranked_causes = sorted(
                cause_likelihoods.items(), key=lambda x: x[1]["likelihood"], reverse=True
            )

            return {
                "status": "success",
                "cause_likelihoods": cause_likelihoods,
                "ranked_causes": [{"cause_id": cid, **data} for cid, data in ranked_causes],
                "most_likely_cause": ranked_causes[0] if ranked_causes else None,
                "observed_effects": observed_effects,
                "total_causes_evaluated": len(possible_causes),
            }

        except Exception as e:
            return {"status": "error", "error": f"Causal retrodiction failed: {str(e)}"}

    def _analyze_intervention(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Analyze the causal effects of a proposed intervention."""
        try:
            intervention = payload.get("intervention", {})
            target_system = payload.get("target_system", {})
            evaluation_metrics = payload.get("metrics", ["effectiveness", "side_effects"])

            analysis_results = {}

            # Effectiveness analysis
            if "effectiveness" in evaluation_metrics:
                effectiveness = self._evaluate_intervention_effectiveness(
                    intervention, target_system
                )
                analysis_results["effectiveness"] = effectiveness

            # Side effects analysis
            if "side_effects" in evaluation_metrics:
                side_effects = self._predict_side_effects(intervention, target_system)
                analysis_results["side_effects"] = side_effects

            # Risk assessment
            if "risk_assessment" in evaluation_metrics:
                risk_assessment = self._assess_intervention_risks(intervention, target_system)
                analysis_results["risk_assessment"] = risk_assessment

            # Overall recommendation
            overall_score = 0.0
            if "effectiveness" in analysis_results:
                overall_score += analysis_results["effectiveness"].get("score", 0) * 0.5
            if "side_effects" in analysis_results:
                side_effect_penalty = analysis_results["side_effects"].get("severity", 0)
                overall_score -= side_effect_penalty * 0.3
            if "risk_assessment" in analysis_results:
                risk_penalty = analysis_results["risk_assessment"].get("risk_level", 0)
                overall_score -= risk_penalty * 0.2

            recommendation = (
                "proceed" if overall_score > 0.6 else "caution" if overall_score > 0.3 else "avoid"
            )

            return {
                "status": "success",
                "intervention": intervention,
                "analysis_results": analysis_results,
                "overall_score": max(0, min(1, overall_score)),
                "recommendation": recommendation,
                "confidence": 0.75,
            }

        except Exception as e:
            return {"status": "error", "error": f"Intervention analysis failed: {str(e)}"}

    def _evaluate_intervention_effectiveness(
        self, intervention: Dict[str, Any], target_system: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Evaluate how effective an intervention would be."""
        # Simple effectiveness heuristic
        intervention_strength = sum(
            abs(v) for v in intervention.values() if isinstance(v, (int, float))
        )
        system_responsiveness = target_system.get("responsiveness", 0.5)

        effectiveness_score = min(1.0, intervention_strength * system_responsiveness)

        return {
            "score": effectiveness_score,
            "method": "heuristic_evaluation",
            "factors": {
                "intervention_strength": intervention_strength,
                "system_responsiveness": system_responsiveness,
            },
        }

    def _predict_side_effects(
        self, intervention: Dict[str, Any], target_system: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Predict potential side effects of an intervention."""
        # Simple side effect prediction
        intervention_complexity = len(intervention)
        system_complexity = len(target_system.get("components", []))

        side_effect_probability = min(1.0, (intervention_complexity * system_complexity) / 50)
        severity = min(1.0, side_effect_probability * 0.8)

        return {
            "probability": side_effect_probability,
            "severity": severity,
            "predicted_effects": [
                f"Unintended modification of {comp}"
                for comp in target_system.get("components", [])[:3]
            ],
        }

    def _assess_intervention_risks(
        self, intervention: Dict[str, Any], target_system: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Assess risks associated with an intervention."""
        # Simple risk assessment
        intervention_magnitude = sum(
            abs(v) for v in intervention.values() if isinstance(v, (int, float))
        )
        system_criticality = target_system.get("criticality", 0.5)

        risk_level = min(1.0, intervention_magnitude * system_criticality)

        return {
            "risk_level": risk_level,
            "risk_category": "high"
            if risk_level > 0.7
            else "medium"
            if risk_level > 0.4
            else "low",
            "risk_factors": [
                "System criticality",
                "Intervention magnitude",
                "Uncertainty in effects",
            ],
        }

    def _forecast_time_series(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Forecast future values of time series data."""
        try:
            time_series = payload.get("time_series", [])
            forecast_horizon = payload.get("horizon", 5)
            method = payload.get("method", "auto")

            if not time_series:
                return {"status": "error", "error": "No time series data provided"}

            forecasts = {}

            # Linear trend forecast
            if method in ["linear_trend", "auto"]:
                linear_forecast = self._linear_trend_forecast(time_series, forecast_horizon)
                forecasts["linear_trend"] = linear_forecast

            # Moving average forecast
            if method in ["moving_average", "auto"]:
                ma_forecast = self._moving_average_forecast(time_series, forecast_horizon)
                forecasts["moving_average"] = ma_forecast

            # Exponential smoothing
            if method in ["exponential_smoothing", "auto"]:
                exp_forecast = self._exponential_smoothing_forecast(time_series, forecast_horizon)
                forecasts["exponential_smoothing"] = exp_forecast

            # Select best forecast if auto mode
            if method == "auto":
                best_method = min(
                    forecasts.keys(), key=lambda k: forecasts[k].get("mse", float("inf"))
                )
                best_forecast = forecasts[best_method]
            else:
                best_forecast = list(forecasts.values())[0] if forecasts else None

            return {
                "status": "success",
                "forecasts": forecasts,
                "best_forecast": best_forecast,
                "method_used": method,
                "forecast_horizon": forecast_horizon,
                "historical_data_points": len(time_series),
            }

        except Exception as e:
            return {"status": "error", "error": f"Time series forecasting failed: {str(e)}"}

    def _linear_trend_forecast(self, time_series: List[float], horizon: int) -> Dict[str, Any]:
        """Simple linear trend forecasting."""
        if len(time_series) < 2:
            return {
                "values": [time_series[-1]] * horizon if time_series else [0] * horizon,
                "mse": float("inf"),
            }

        # Calculate linear trend
        x = list(range(len(time_series)))
        y = time_series

        # Simple linear regression
        n = len(x)
        sum_x = sum(x)
        sum_y = sum(y)
        sum_xy = sum(x[i] * y[i] for i in range(n))
        sum_x2 = sum(x[i] ** 2 for i in range(n))

        slope = (n * sum_xy - sum_x * sum_y) / (n * sum_x2 - sum_x**2)
        intercept = (sum_y - slope * sum_x) / n

        # Forecast future values
        forecast_values = []
        for i in range(horizon):
            future_x = len(time_series) + i
            forecast_value = slope * future_x + intercept
            forecast_values.append(forecast_value)

        # Calculate MSE on historical data
        predicted = [slope * x[i] + intercept for i in range(n)]
        mse = sum((y[i] - predicted[i]) ** 2 for i in range(n)) / n

        return {"values": forecast_values, "slope": slope, "intercept": intercept, "mse": mse}

    def _moving_average_forecast(
        self, time_series: List[float], horizon: int, window: int = 3
    ) -> Dict[str, Any]:
        """Moving average forecasting."""
        if len(time_series) < window:
            window = len(time_series)

        # Calculate moving average
        recent_values = time_series[-window:]
        moving_avg = sum(recent_values) / len(recent_values)

        # Forecast (assume constant at moving average)
        forecast_values = [moving_avg] * horizon

        # Calculate MSE on historical data
        mse = 0.0
        if len(time_series) > window:
            predictions = []
            for i in range(window, len(time_series)):
                window_values = time_series[i - window : i]
                pred = sum(window_values) / len(window_values)
                predictions.append(pred)
                mse += (time_series[i] - pred) ** 2

            mse /= len(predictions) if predictions else 1

        return {
            "values": forecast_values,
            "window_size": window,
            "moving_average": moving_avg,
            "mse": mse,
        }

    def _exponential_smoothing_forecast(
        self, time_series: List[float], horizon: int, alpha: float = 0.3
    ) -> Dict[str, Any]:
        """Exponential smoothing forecasting."""
        if not time_series:
            return {"values": [0] * horizon, "mse": float("inf")}

        # Initialize with first value
        smoothed = [time_series[0]]

        # Calculate exponentially smoothed values
        for i in range(1, len(time_series)):
            smoothed_value = alpha * time_series[i] + (1 - alpha) * smoothed[-1]
            smoothed.append(smoothed_value)

        # Forecast (constant at last smoothed value)
        last_smoothed = smoothed[-1]
        forecast_values = [last_smoothed] * horizon

        # Calculate MSE
        mse = sum((time_series[i] - smoothed[i]) ** 2 for i in range(len(time_series))) / len(
            time_series
        )

        return {
            "values": forecast_values,
            "alpha": alpha,
            "last_smoothed_value": last_smoothed,
            "mse": mse,
        }

    def _test_hypothesis(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Test a scientific hypothesis using available data."""
        try:
            hypothesis = payload.get("hypothesis", "")
            data = payload.get("data", [])
            test_type = payload.get("test_type", "correlation")
            significance_level = payload.get("significance_level", 0.05)

            if test_type == "correlation" and len(data) >= 2:
                return self._test_correlation_hypothesis(hypothesis, data, significance_level)
            elif test_type == "mean_difference" and len(data) >= 2:
                return self._test_mean_difference(hypothesis, data, significance_level)
            else:
                return {
                    "status": "error",
                    "error": f"Unsupported test type or insufficient data: {test_type}",
                    "supported_tests": ["correlation", "mean_difference"],
                }

        except Exception as e:
            return {"status": "error", "error": f"Hypothesis testing failed: {str(e)}"}

    def _test_correlation_hypothesis(
        self, hypothesis: str, data: List[Dict[str, Any]], significance_level: float
    ) -> Dict[str, Any]:
        """Test correlation hypothesis between variables."""
        # Extract numeric variables from data
        variables = {}
        for record in data:
            for key, value in record.items():
                if isinstance(value, (int, float)):
                    if key not in variables:
                        variables[key] = []
                    variables[key].append(value)

        if len(variables) < 2:
            return {
                "status": "error",
                "error": "Need at least 2 numeric variables for correlation test",
            }

        # Calculate correlations between all pairs
        var_names = list(variables.keys())
        correlations = {}

        for i in range(len(var_names)):
            for j in range(i + 1, len(var_names)):
                var1, var2 = var_names[i], var_names[j]
                values1, values2 = variables[var1], variables[var2]

                # Ensure same length
                min_len = min(len(values1), len(values2))
                values1, values2 = values1[:min_len], values2[:min_len]

                if min_len > 1:
                    # Simple correlation calculation
                    mean1, mean2 = sum(values1) / len(values1), sum(values2) / len(values2)

                    numerator = sum(
                        (values1[k] - mean1) * (values2[k] - mean2) for k in range(min_len)
                    )
                    denom1 = sum((values1[k] - mean1) ** 2 for k in range(min_len))
                    denom2 = sum((values2[k] - mean2) ** 2 for k in range(min_len))

                    if denom1 > 0 and denom2 > 0:
                        correlation = numerator / (denom1 * denom2) ** 0.5
                        correlations[f"{var1}_vs_{var2}"] = {
                            "correlation": correlation,
                            "variables": [var1, var2],
                            "sample_size": min_len,
                            "significant": abs(correlation)
                            > (1.96 / (min_len**0.5)),  # Rough significance test
                        }

        return {
            "status": "success",
            "hypothesis": hypothesis,
            "test_type": "correlation",
            "correlations": correlations,
            "significance_level": significance_level,
            "conclusion": "Correlations found"
            if any(c["significant"] for c in correlations.values())
            else "No significant correlations",
        }

    def _build_causal_model(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Build a structural causal model from data."""
        try:
            data = payload.get("data", [])
            variables = payload.get("variables", [])
            causal_structure = payload.get("causal_structure", {})
            model_id = payload.get("model_id", "default")

            if not data:
                return {"status": "error", "error": "No data provided for model building"}

            # Build SCM
            scm = SCMImplementation(dag=causal_structure)
            success = scm.fit(data)

            if success:
                # Store the model
                self.scm_models[model_id] = scm

                # Extract model statistics
                model_stats = {
                    "num_variables": len(scm.dag),
                    "num_parameters": len(scm.parameters),
                    "training_samples": len(data),
                    "causal_edges": sum(len(parents) for parents in scm.dag.values()),
                }

                return {
                    "status": "success",
                    "model_id": model_id,
                    "model_statistics": model_stats,
                    "causal_structure": causal_structure,
                    "variables": variables,
                    "fitted_successfully": True,
                }
            else:
                return {"status": "error", "error": "Failed to fit structural causal model to data"}

        except Exception as e:
            return {"status": "error", "error": f"Causal model building failed: {str(e)}"}


class TelosWorker:
    """
    Main TELOS worker class that handles RabbitMQ communication
    and orchestrates the core scientific reasoning operations.
    """

    def __init__(self):
        self.logger = logging.getLogger("TELOS_WORKER")
        self.core_engine = TelosCoreEngine()
        self.connection = None
        self.channel = None
        self.is_running = False

        # Setup graceful shutdown handling
        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)

        self._connect_to_rabbitmq()
        self.logger.info("TELOS Worker initialized successfully")

    def _connect_to_rabbitmq(self):
        """Establish connection to RabbitMQ with retry logic."""
        max_retries = 10
        retry_delay = 5

        for attempt in range(1, max_retries + 1):
            try:
                credentials = pika.PlainCredentials("guest", "guest")
                parameters = pika.ConnectionParameters(
                    host=RABBITMQ_HOST,
                    port=RABBITMQ_PORT,
                    credentials=credentials,
                    heartbeat=600,
                    blocked_connection_timeout=300,
                )

                self.connection = pika.BlockingConnection(parameters)
                self.channel = self.connection.channel()

                self._setup_queues()

                self.logger.info(
                    f"Successfully connected to RabbitMQ at {RABBITMQ_HOST}:{RABBITMQ_PORT}"
                )
                return

            except pika.exceptions.AMQPConnectionError as e:
                self.logger.warning(
                    f"Attempt {attempt}/{max_retries}: Failed to connect to RabbitMQ: {e}"
                )
                if attempt < max_retries:
                    self.logger.info(f"Retrying in {retry_delay} seconds...")
                    time.sleep(retry_delay)
                else:
                    self.logger.error("Could not connect to RabbitMQ after all attempts. Exiting.")
                    sys.exit(1)
            except Exception as e:
                self.logger.error(f"Unexpected error connecting to RabbitMQ: {e}")
                sys.exit(1)

    def _setup_queues(self):
        """Declare and configure queues."""
        try:
            self.channel.queue_declare(queue=TASK_QUEUE, durable=True)
            self.channel.queue_declare(queue=RESULT_QUEUE, durable=True)
            self.channel.basic_qos(prefetch_count=1)

            self.logger.info(f"Queues configured: {TASK_QUEUE} -> {RESULT_QUEUE}")

        except Exception as e:
            self.logger.error(f"Failed to setup queues: {e}")
            raise

    def process_task(self, ch, method, properties, body):
        """Process incoming task messages."""
        start_time = time.time()
        task_id = "unknown"

        try:
            # Parse message
            task = json.loads(body.decode("utf-8"))
            task_id = task.get("task_id", f"telos_{int(time.time() * 1000)}")
            workflow_id = task.get("workflow_id", "unknown")
            task_type = task.get("type", "unknown")
            payload = task.get("payload", {})

            self.logger.info(
                f"Processing task {task_id} (workflow: {workflow_id}) of type: {task_type}"
            )

            # Execute task using core engine
            result_payload = self.core_engine.execute(task_type, payload)
            status = "success" if result_payload.get("status") == "success" else "failure"

            processing_time = time.time() - start_time

            # Prepare response
            response = {
                "subsystem": SUBSYSTEM_NAME,
                "task_id": task_id,
                "workflow_id": workflow_id,
                "status": status,
                "result": result_payload,
                "processing_time": processing_time,
                "timestamp": datetime.utcnow().isoformat(),
            }

            # Publish result
            self.channel.basic_publish(
                exchange="",
                routing_key=RESULT_QUEUE,
                body=json.dumps(response),
                properties=pika.BasicProperties(
                    delivery_mode=2, correlation_id=task_id  # Make message persistent
                ),
            )

            self.logger.info(
                f"Task {task_id} completed in {processing_time:.3f}s with status: {status}"
            )

        except json.JSONDecodeError as e:
            self.logger.error(f"Invalid JSON in task {task_id}: {e}")
            self._send_error_response(task_id, f"Invalid JSON: {str(e)}")
        except Exception as e:
            self.logger.error(f"Error processing task {task_id}: {e}", exc_info=True)
            self._send_error_response(task_id, str(e))
        finally:
            # Always acknowledge the message
            try:
                ch.basic_ack(delivery_tag=method.delivery_tag)
            except Exception as e:
                self.logger.error(f"Failed to acknowledge message: {e}")

    def _send_error_response(self, task_id: str, error_message: str):
        """Send error response for failed tasks."""
        try:
            error_response = {
                "subsystem": SUBSYSTEM_NAME,
                "task_id": task_id,
                "status": "error",
                "error": error_message,
                "timestamp": datetime.utcnow().isoformat(),
            }

            self.channel.basic_publish(
                exchange="",
                routing_key=RESULT_QUEUE,
                body=json.dumps(error_response),
                properties=pika.BasicProperties(correlation_id=task_id),
            )
        except Exception as e:
            self.logger.error(f"Failed to send error response: {e}")

    def start_consuming(self):
        """Start consuming messages from the task queue."""
        try:
            self.channel.basic_consume(queue=TASK_QUEUE, on_message_callback=self.process_task)

            self.is_running = True
            self.logger.info(
                f"{SUBSYSTEM_NAME} Worker started and listening on queue: {TASK_QUEUE}"
            )

            self.channel.start_consuming()

        except KeyboardInterrupt:
            self.logger.info("Received interrupt signal, shutting down gracefully...")
            self._shutdown()
        except Exception as e:
            self.logger.error(f"Error in consumer loop: {e}")
            self._shutdown()

    def _signal_handler(self, signum, frame):
        """Handle system signals for graceful shutdown."""
        self.logger.info(f"Received signal {signum}, initiating shutdown...")
        self._shutdown()

    def _shutdown(self):
        """Gracefully shutdown the worker."""
        if self.is_running:
            self.is_running = False

            # Stop consuming messages
            if self.channel and self.channel.is_open:
                try:
                    self.channel.stop_consuming()
                    self.logger.info("Stopped consuming messages")
                except Exception as e:
                    self.logger.error(f"Error stopping consumer: {e}")

            # Close connections
            if self.connection and self.connection.is_open:
                try:
                    self.connection.close()
                    self.logger.info("RabbitMQ connection closed")
                except Exception as e:
                    self.logger.error(f"Error closing connection: {e}")

            self.logger.info("TELOS Worker shutdown complete")


def main():
    """Main entry point for the TELOS worker."""
    try:
        worker = TelosWorker()
        worker.start_consuming()
    except Exception as e:
        logging.error(f"Failed to start TELOS worker: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
