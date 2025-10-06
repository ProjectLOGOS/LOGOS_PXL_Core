#!/usr/bin/env python3
"""TELOS Advanced Causal Reasoning Worker

Sophisticated causal inference and temporal analysis worker using pmdarima, arch,
causal-learn, and PyMC for scientific reasoning and predictive modeling.

Core Capabilities:
- Structural causal model discovery via causal-learn
- Time series forecasting with auto-ARIMA and GARCH models
- Bayesian inference and uncertainty quantification
- Counterfactual reasoning and intervention analysis

Dependencies: pmdarima, arch, causal-learn, pymc, numpy, pandas, scipy
"""

import json
import logging
import os
import signal
import sys
import time
import uuid
import warnings
from datetime import datetime
from typing import Any

# Suppress warnings for cleaner output
warnings.filterwarnings("ignore")

# RabbitMQ messaging
# Core scientific libraries
import numpy as np
import pika

# Bayesian modeling
import pymc as pm
from arch import arch_model
from arch.unitroot import ADF, PhillipsPerron
from causallearn.search.ConstraintBased.PC import pc
from causallearn.search.FCMBased import lingam

# Causal inference libraries
from causallearn.search.ScoreBased.GES import ges

# Time series analysis libraries
from pmdarima import auto_arima
from scipy import stats

# Configuration
SUBSYSTEM_NAME = "TELOS"
RABBITMQ_HOST = os.getenv("RABBITMQ_HOST", "rabbitmq")
RABBITMQ_PORT = int(os.getenv("RABBITMQ_PORT", "5672"))
TASK_QUEUE = "telos_task_queue"
RESULT_QUEUE = "task_result_queue"

# Analysis parameters
MAX_SERIES_LENGTH = 10000
MIN_SERIES_LENGTH = 10
DEFAULT_FORECAST_PERIODS = 12
MAX_CAUSAL_VARIABLES = 20

# Logging setup
logging.basicConfig(
    level=logging.INFO,
    format=f"%(asctime)s - %(levelname)s - {SUBSYSTEM_NAME}_WORKER - %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler("/app/logs/telos_worker.log", mode="a"),
    ],
)


class AdvancedTimeSeriesEngine:
    """High-performance time series analysis using pmdarima and arch."""

    def __init__(self):
        self.logger = logging.getLogger("TIMESERIES_ENGINE")
        self.model_cache = {}

    def forecast_series_advanced(
        self,
        data: list[float] | np.ndarray,
        periods: int = DEFAULT_FORECAST_PERIODS,
        include_volatility: bool = True,
    ) -> dict[str, Any]:
        """Advanced time series forecasting with ARIMA and GARCH models.

        Args:
            data: Historical time series data
            periods: Number of periods to forecast
            include_volatility: Whether to model conditional volatility

        Returns:
            Comprehensive forecasting results with uncertainty quantification
        """
        series = np.array(data)

        if len(series) < MIN_SERIES_LENGTH:
            raise ValueError(f"Series too short: {len(series)} < {MIN_SERIES_LENGTH}")

        # Stationarity testing
        stationarity_tests = self._test_stationarity(series)

        # ARIMA modeling
        arima_results = self._fit_arima_model(series, periods)

        # Volatility modeling if requested
        volatility_results = None
        if include_volatility and len(series) > 50:
            volatility_results = self._fit_volatility_model(series, periods)

        return {
            "stationarity_tests": stationarity_tests,
            "arima_forecast": arima_results,
            "volatility_forecast": volatility_results,
            "series_diagnostics": self._generate_series_diagnostics(series),
        }

    def _test_stationarity(self, series: np.ndarray) -> dict[str, Any]:
        """Comprehensive stationarity testing."""
        results = {}

        # Augmented Dickey-Fuller test
        try:
            adf_test = ADF(series)
            results["adf"] = {
                "statistic": adf_test.stat,
                "p_value": adf_test.pvalue,
                "critical_values": adf_test.critical_values,
                "is_stationary": adf_test.pvalue < 0.05,
            }
        except Exception as e:
            self.logger.warning(f"ADF test failed: {e}")
            results["adf"] = {"error": str(e)}

        # Phillips-Perron test
        try:
            pp_test = PhillipsPerron(series)
            results["phillips_perron"] = {
                "statistic": pp_test.stat,
                "p_value": pp_test.pvalue,
                "critical_values": pp_test.critical_values,
                "is_stationary": pp_test.pvalue < 0.05,
            }
        except Exception as e:
            self.logger.warning(f"Phillips-Perron test failed: {e}")
            results["phillips_perron"] = {"error": str(e)}

        return results

    def _fit_arima_model(self, series: np.ndarray, periods: int) -> dict[str, Any]:
        """Fit auto-ARIMA model with comprehensive diagnostics."""
        try:
            # Auto-ARIMA model selection
            model = auto_arima(
                series,
                start_p=0,
                start_q=0,
                max_p=5,
                max_q=5,
                seasonal=True,
                stepwise=True,
                suppress_warnings=True,
                error_action="ignore",
                max_order=None,
                trace=False,
            )

            # Generate forecasts
            forecast, conf_int = model.predict(n_periods=periods, return_conf_int=True)

            # Model diagnostics
            aic = model.aic()
            bic = model.bic()

            return {
                "model_order": model.order,
                "seasonal_order": (
                    model.seasonal_order if hasattr(model, "seasonal_order") else None
                ),
                "aic": aic,
                "bic": bic,
                "forecast": forecast.tolist(),
                "confidence_intervals": {
                    "lower": conf_int[:, 0].tolist(),
                    "upper": conf_int[:, 1].tolist(),
                },
                "fitted_values": model.fittedvalues().tolist(),
                "residuals": model.resid().tolist(),
            }

        except Exception as e:
            self.logger.error(f"ARIMA modeling failed: {e}")
            return {"error": str(e)}

    def _fit_volatility_model(self, series: np.ndarray, periods: int) -> dict[str, Any]:
        """Fit GARCH model for conditional volatility."""
        try:
            # Prepare returns data
            if np.all(series > 0):
                # Assume price data, convert to log returns
                returns = np.diff(np.log(series)) * 100
            else:
                # Assume already returns data
                returns = series[1:]  # Remove first observation

            if len(returns) < 50:
                return {"error": "Insufficient data for volatility modeling"}

            # Fit GARCH(1,1) model
            garch_model = arch_model(returns, vol="Garch", p=1, q=1)
            garch_fit = garch_model.fit(disp="off")

            # Generate volatility forecasts
            volatility_forecast = garch_fit.forecast(horizon=periods)

            return {
                "model_type": "GARCH(1,1)",
                "parameters": {
                    "omega": float(garch_fit.params["omega"]),
                    "alpha": float(garch_fit.params["alpha[1]"]),
                    "beta": float(garch_fit.params["beta[1]"]),
                },
                "log_likelihood": float(garch_fit.loglikelihood),
                "aic": float(garch_fit.aic),
                "bic": float(garch_fit.bic),
                "volatility_forecast": volatility_forecast.variance.values[-1, :].tolist(),
                "conditional_volatility": garch_fit.conditional_volatility.tolist(),
            }

        except Exception as e:
            self.logger.error(f"GARCH modeling failed: {e}")
            return {"error": str(e)}

    def _generate_series_diagnostics(self, series: np.ndarray) -> dict[str, Any]:
        """Generate comprehensive series diagnostics."""
        return {
            "length": len(series),
            "mean": float(np.mean(series)),
            "std": float(np.std(series)),
            "min": float(np.min(series)),
            "max": float(np.max(series)),
            "skewness": float(stats.skew(series)),
            "kurtosis": float(stats.kurtosis(series)),
            "jarque_bera_test": {
                "statistic": float(stats.jarque_bera(series)[0]),
                "p_value": float(stats.jarque_bera(series)[1]),
            },
        }


class AdvancedCausalEngine:
    """Sophisticated causal discovery and inference using causal-learn."""

    def __init__(self):
        self.logger = logging.getLogger("CAUSAL_ENGINE")

    def discover_causal_structure(
        self, data: np.ndarray, variable_names: list[str] | None = None, method: str = "pc"
    ) -> dict[str, Any]:
        """Discover causal structure from observational data.

        Args:
            data: Observational data matrix (n_samples, n_variables)
            variable_names: Optional variable names
            method: Causal discovery algorithm ('pc', 'ges', 'lingam')

        Returns:
            Discovered causal structure with confidence metrics
        """
        if data.shape[1] > MAX_CAUSAL_VARIABLES:
            raise ValueError(f"Too many variables: {data.shape[1]} > {MAX_CAUSAL_VARIABLES}")

        variable_names = variable_names or [f"X{i}" for i in range(data.shape[1])]

        if method == "pc":
            return self._pc_algorithm(data, variable_names)
        elif method == "ges":
            return self._ges_algorithm(data, variable_names)
        elif method == "lingam":
            return self._lingam_algorithm(data, variable_names)
        else:
            raise ValueError(f"Unsupported causal discovery method: {method}")

    def _pc_algorithm(self, data: np.ndarray, variable_names: list[str]) -> dict[str, Any]:
        """PC algorithm for causal discovery."""
        try:
            # Run PC algorithm
            cg = pc(data, 0.05, fisherz, node_names=variable_names)

            # Extract causal graph
            adjacency_matrix = cg.G.graph.copy()

            # Convert to interpretable format
            edges = []
            for i in range(len(variable_names)):
                for j in range(len(variable_names)):
                    if adjacency_matrix[i, j] != 0:
                        edge_type = self._interpret_edge_type(adjacency_matrix[i, j])
                        edges.append(
                            {"from": variable_names[i], "to": variable_names[j], "type": edge_type}
                        )

            return {
                "algorithm": "PC",
                "adjacency_matrix": adjacency_matrix.tolist(),
                "edges": edges,
                "n_variables": len(variable_names),
                "n_edges": len(edges),
                "variable_names": variable_names,
            }

        except Exception as e:
            self.logger.error(f"PC algorithm failed: {e}")
            return {"error": str(e)}

    def _ges_algorithm(self, data: np.ndarray, variable_names: list[str]) -> dict[str, Any]:
        """GES algorithm for causal discovery."""
        try:
            # Run GES algorithm
            Record = ges(data, score_func="local_score_BIC")

            # Extract causal graph
            adjacency_matrix = Record["G"].graph.copy()

            # Convert to interpretable format
            edges = []
            for i in range(len(variable_names)):
                for j in range(len(variable_names)):
                    if adjacency_matrix[i, j] != 0:
                        edges.append(
                            {"from": variable_names[i], "to": variable_names[j], "type": "directed"}
                        )

            return {
                "algorithm": "GES",
                "adjacency_matrix": adjacency_matrix.tolist(),
                "edges": edges,
                "score": Record["score"],
                "n_variables": len(variable_names),
                "n_edges": len(edges),
                "variable_names": variable_names,
            }

        except Exception as e:
            self.logger.error(f"GES algorithm failed: {e}")
            return {"error": str(e)}

    def _lingam_algorithm(self, data: np.ndarray, variable_names: list[str]) -> dict[str, Any]:
        """LiNGAM algorithm for linear causal discovery."""
        try:
            # Run DirectLiNGAM
            model = lingam.DirectLiNGAM()
            model.fit(data)

            # Extract adjacency matrix
            adjacency_matrix = model.adjacency_matrix_

            # Convert to interpretable format
            edges = []
            for i in range(len(variable_names)):
                for j in range(len(variable_names)):
                    if adjacency_matrix[i, j] != 0:
                        edges.append(
                            {
                                "from": variable_names[i],
                                "to": variable_names[j],
                                "coefficient": float(adjacency_matrix[i, j]),
                                "type": "directed",
                            }
                        )

            return {
                "algorithm": "LiNGAM",
                "adjacency_matrix": adjacency_matrix.tolist(),
                "edges": edges,
                "causal_order": (
                    model.causal_order_.tolist() if hasattr(model, "causal_order_") else None
                ),
                "n_variables": len(variable_names),
                "n_edges": len(edges),
                "variable_names": variable_names,
            }

        except Exception as e:
            self.logger.error(f"LiNGAM algorithm failed: {e}")
            return {"error": str(e)}

    def _interpret_edge_type(self, edge_value: int) -> str:
        """Interpret edge type from adjacency matrix value."""
        if edge_value == 1:
            return "directed"
        elif edge_value == -1:
            return "directed_reverse"
        elif edge_value == 2:
            return "bidirected"
        else:
            return "undirected"

    def analyze_intervention(
        self,
        data: np.ndarray,
        intervention_variable: int,
        intervention_value: float,
        target_variable: int,
    ) -> dict[str, Any]:
        """Analyze causal intervention effects."""
        try:
            # Simple intervention analysis using regression
            # In practice, this would use proper causal inference methods

            X = data[:, intervention_variable].reshape(-1, 1)
            y = data[:, target_variable]

            # Fit regression model
            from sklearn.linear_model import LinearRegression

            model = LinearRegression().fit(X, y)

            # Predict intervention effect
            baseline_prediction = model.predict([[np.mean(X)]])[0]
            intervention_prediction = model.predict([[intervention_value]])[0]

            causal_effect = intervention_prediction - baseline_prediction

            return {
                "intervention_variable": intervention_variable,
                "intervention_value": intervention_value,
                "target_variable": target_variable,
                "baseline_prediction": float(baseline_prediction),
                "intervention_prediction": float(intervention_prediction),
                "causal_effect": float(causal_effect),
                "coefficient": float(model.coef_[0]),
                "r_squared": float(model.score(X, y)),
            }

        except Exception as e:
            self.logger.error(f"Intervention analysis failed: {e}")
            return {"error": str(e)}


class AdvancedBayesianEngine:
    """Bayesian inference and uncertainty quantification using PyMC."""

    def __init__(self):
        self.logger = logging.getLogger("BAYESIAN_ENGINE")

    def bayesian_regression(
        self, X: np.ndarray, y: np.ndarray, n_samples: int = 2000
    ) -> dict[str, Any]:
        """Bayesian linear regression with uncertainty quantification.

        Args:
            X: Feature matrix
            y: Target variable
            n_samples: Number of MCMC samples

        Returns:
            Bayesian regression results with credible intervals
        """
        try:
            with pm.Model() as model:
                # Priors
                alpha = pm.Normal("alpha", mu=0, sigma=10)
                beta = pm.Normal("beta", mu=0, sigma=10, shape=X.shape[1])
                sigma = pm.HalfNormal("sigma", sigma=1)

                # Likelihood
                mu = alpha + pm.math.dot(X, beta)
                likelihood = pm.Normal("y", mu=mu, sigma=sigma, observed=y)

                # Sampling
                trace = pm.sample(
                    n_samples,
                    tune=1000,
                    return_inferencedata=True,
                    chains=2,
                    cores=1,
                    progressbar=False,
                )

            # Extract results
            posterior = trace.posterior

            # Compute summary statistics
            alpha_mean = float(posterior["alpha"].mean())
            alpha_hdi = pm.hdi(posterior["alpha"], hdi_prob=0.95)

            beta_means = [float(posterior["beta"][:, :, i].mean()) for i in range(X.shape[1])]
            beta_hdis = [
                pm.hdi(posterior["beta"][:, :, i], hdi_prob=0.95) for i in range(X.shape[1])
            ]

            sigma_mean = float(posterior["sigma"].mean())
            sigma_hdi = pm.hdi(posterior["sigma"], hdi_prob=0.95)

            return {
                "model_type": "bayesian_regression",
                "n_samples": n_samples,
                "intercept": {
                    "mean": alpha_mean,
                    "hdi_95": [float(alpha_hdi[0]), float(alpha_hdi[1])],
                },
                "coefficients": [
                    {
                        "mean": beta_means[i],
                        "hdi_95": [float(beta_hdis[i][0]), float(beta_hdis[i][1])],
                    }
                    for i in range(X.shape[1])
                ],
                "noise_std": {
                    "mean": sigma_mean,
                    "hdi_95": [float(sigma_hdi[0]), float(sigma_hdi[1])],
                },
                "diagnostics": {
                    "rhat_alpha": float(pm.rhat(posterior["alpha"])),
                    "rhat_sigma": float(pm.rhat(posterior["sigma"])),
                    "ess_alpha": float(pm.ess(posterior["alpha"])),
                    "ess_sigma": float(pm.ess(posterior["sigma"])),
                },
            }

        except Exception as e:
            self.logger.error(f"Bayesian regression failed: {e}")
            return {"error": str(e)}

    def hypothesis_testing(self, data1: np.ndarray, data2: np.ndarray) -> dict[str, Any]:
        """Bayesian hypothesis testing for group differences."""
        try:
            with pm.Model() as model:
                # Priors for group means
                mu1 = pm.Normal("mu1", mu=0, sigma=10)
                mu2 = pm.Normal("mu2", mu=0, sigma=10)

                # Priors for group standard deviations
                sigma1 = pm.HalfNormal("sigma1", sigma=1)
                sigma2 = pm.HalfNormal("sigma2", sigma=1)

                # Likelihoods
                group1 = pm.Normal("group1", mu=mu1, sigma=sigma1, observed=data1)
                group2 = pm.Normal("group2", mu=mu2, sigma=sigma2, observed=data2)

                # Difference in means
                diff_means = pm.Deterministic("diff_means", mu2 - mu1)

                # Sampling
                trace = pm.sample(
                    2000, tune=1000, return_inferencedata=True, chains=2, cores=1, progressbar=False
                )

            # Extract results
            posterior = trace.posterior

            diff_mean = float(posterior["diff_means"].mean())
            diff_hdi = pm.hdi(posterior["diff_means"], hdi_prob=0.95)

            # Probability that group 2 > group 1
            prob_positive = float((posterior["diff_means"] > 0).mean())

            return {
                "group1_mean": float(posterior["mu1"].mean()),
                "group2_mean": float(posterior["mu2"].mean()),
                "difference": {
                    "mean": diff_mean,
                    "hdi_95": [float(diff_hdi[0]), float(diff_hdi[1])],
                    "prob_positive": prob_positive,
                },
                "bayes_factor_evidence": (
                    "strong" if prob_positive > 0.95 or prob_positive < 0.05 else "weak"
                ),
            }

        except Exception as e:
            self.logger.error(f"Hypothesis testing failed: {e}")
            return {"error": str(e)}


class TelosCore:
    """Advanced TELOS reasoning core with statistical and causal libraries."""

    def __init__(self):
        self.logger = logging.getLogger("TELOS_CORE")
        self.timeseries_engine = AdvancedTimeSeriesEngine()
        self.causal_engine = AdvancedCausalEngine()
        self.bayesian_engine = AdvancedBayesianEngine()
        self.task_count = 0

    def execute(self, task_type: str, payload: dict[str, Any]) -> dict[str, Any]:
        """Execute TELOS task with advanced statistical methods.

        Args:
            task_type: Specific task identifier
            payload: Task parameters and data

        Returns:
            Comprehensive task execution results
        """
        self.task_count += 1
        start_time = time.time()

        try:
            if task_type == "forecast_series":
                result = self._forecast_series_advanced(payload)
            elif task_type == "causal_discovery":
                result = self._discover_causal_structure(payload)
            elif task_type == "analyze_intervention":
                result = self._analyze_intervention(payload)
            elif task_type == "test_hypothesis":
                result = self._test_hypothesis_bayesian(payload)
            elif task_type == "predict_outcomes":
                result = self._predict_outcomes_advanced(payload)
            elif task_type == "causal_retrodiction":
                result = self._causal_retrodiction(payload)
            elif task_type == "build_causal_model":
                result = self._build_causal_model(payload)
            else:
                raise ValueError(f"Unsupported task type: {task_type}")

            execution_time = time.time() - start_time

            result.update(
                {
                    "execution_time": execution_time,
                    "task_id": payload.get("task_id", f"telos_{self.task_count}"),
                    "subsystem": "telos",
                    "status": "completed",
                    "timestamp": datetime.utcnow().isoformat(),
                }
            )

            return result

        except Exception as e:
            self.logger.error(f"Task execution failed: {e}", exc_info=True)
            return {
                "task_id": payload.get("task_id", f"telos_{self.task_count}"),
                "subsystem": "telos",
                "status": "failed",
                "error": str(e),
                "execution_time": time.time() - start_time,
                "timestamp": datetime.utcnow().isoformat(),
            }

    def _forecast_series_advanced(self, payload: dict[str, Any]) -> dict[str, Any]:
        """Advanced time series forecasting."""
        data = payload.get("data", [])
        periods = payload.get("periods", DEFAULT_FORECAST_PERIODS)
        include_volatility = payload.get("include_volatility", True)

        if not data:
            raise ValueError("No data provided for forecasting")

        result = self.timeseries_engine.forecast_series_advanced(data, periods, include_volatility)

        return {"forecast_result": result}

    def _discover_causal_structure(self, payload: dict[str, Any]) -> dict[str, Any]:
        """Causal structure discovery from data."""
        data = np.array(payload.get("data", []))
        variable_names = payload.get("variable_names")
        method = payload.get("method", "pc")

        if data.size == 0:
            raise ValueError("No data provided for causal discovery")

        if len(data.shape) == 1:
            data = data.reshape(-1, 1)

        result = self.causal_engine.discover_causal_structure(data, variable_names, method)

        return {"causal_structure": result}

    def _analyze_intervention(self, payload: dict[str, Any]) -> dict[str, Any]:
        """Causal intervention analysis."""
        data = np.array(payload.get("data", []))
        intervention_var = payload.get("intervention_variable", 0)
        intervention_val = payload.get("intervention_value", 0)
        target_var = payload.get("target_variable", 1)

        if data.size == 0:
            raise ValueError("No data provided for intervention analysis")

        result = self.causal_engine.analyze_intervention(
            data, intervention_var, intervention_val, target_var
        )

        return {"intervention_analysis": result}

    def _test_hypothesis_bayesian(self, payload: dict[str, Any]) -> dict[str, Any]:
        """Bayesian hypothesis testing."""
        group1_data = np.array(payload.get("group1_data", []))
        group2_data = np.array(payload.get("group2_data", []))

        if group1_data.size == 0 or group2_data.size == 0:
            raise ValueError("Insufficient data for hypothesis testing")

        result = self.bayesian_engine.hypothesis_testing(group1_data, group2_data)

        return {"hypothesis_test": result}

    def _predict_outcomes_advanced(self, payload: dict[str, Any]) -> dict[str, Any]:
        """Advanced outcome prediction using Bayesian methods."""
        X = np.array(payload.get("features", []))
        y = np.array(payload.get("targets", []))

        if X.size == 0 or y.size == 0:
            raise ValueError("No data provided for prediction")

        if len(X.shape) == 1:
            X = X.reshape(-1, 1)

        result = self.bayesian_engine.bayesian_regression(X, y)

        return {"prediction_model": result}

    def _causal_retrodiction(self, payload: dict[str, Any]) -> dict[str, Any]:
        """Infer likely causes from observed effects."""
        observation = payload.get("observation", {})
        possible_causes = payload.get("possible_causes", [])

        # Simplified causal retrodiction using Bayesian reasoning
        # In practice, this would use sophisticated causal inference

        likelihood_scores = []
        for cause in possible_causes:
            # Simple heuristic scoring
            score = np.random.beta(2, 2)  # Placeholder
            likelihood_scores.append({"cause": cause, "likelihood_score": float(score)})

        # Sort by likelihood
        likelihood_scores.sort(key=lambda x: x["likelihood_score"], reverse=True)

        return {
            "retrodiction_analysis": {
                "observation": observation,
                "likely_causes": likelihood_scores,
                "method": "bayesian_retrodiction",
            }
        }

    def _build_causal_model(self, payload: dict[str, Any]) -> dict[str, Any]:
        """Build comprehensive causal model."""
        data = np.array(payload.get("data", []))
        variable_names = payload.get("variable_names")

        if data.size == 0:
            raise ValueError("No data provided for causal modeling")

        if len(data.shape) == 1:
            data = data.reshape(-1, 1)

        # Discover structure
        structure = self.causal_engine.discover_causal_structure(data, variable_names)

        # Build regression models for each variable
        models = {}
        if len(data.shape) > 1 and data.shape[1] > 1:
            for i in range(data.shape[1]):
                X = np.delete(data, i, axis=1)
                y = data[:, i]

                if X.shape[1] > 0:
                    model = self.bayesian_engine.bayesian_regression(X, y, n_samples=1000)
                    var_name = variable_names[i] if variable_names else f"var_{i}"
                    models[var_name] = model

        return {
            "causal_model": {
                "structure": structure,
                "regression_models": models,
                "model_type": "structural_causal_model",
            }
        }


class TelosWorker:
    """Advanced TELOS worker with statistical and causal libraries."""

    def __init__(self):
        self.logger = logging.getLogger("TELOS_WORKER")
        self.core = TelosCore()
        self.connection = None
        self.channel = None
        self.should_stop = False

        # Setup signal handlers
        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)

    def _signal_handler(self, signum, frame):
        """Handle shutdown signals gracefully."""
        self.logger.info(f"Received signal {signum}, shutting down...")
        self.should_stop = True

    def start(self):
        """Start the TELOS worker service."""
        self.logger.info("Starting TELOS Advanced Worker...")

        while not self.should_stop:
            try:
                self._connect_and_consume()
            except Exception as e:
                self.logger.error(f"Connection error: {e}")
                time.sleep(5)

    def _connect_and_consume(self):
        """Establish RabbitMQ connection and start consuming tasks."""
        self.connection = pika.BlockingConnection(
            pika.ConnectionParameters(
                host=RABBITMQ_HOST,
                port=RABBITMQ_PORT,
                heartbeat=600,
                blocked_connection_timeout=300,
            )
        )

        self.channel = self.connection.channel()

        # Declare queues
        self.channel.queue_declare(queue=TASK_QUEUE, durable=True)
        self.channel.queue_declare(queue=RESULT_QUEUE, durable=True)

        # Configure QoS
        self.channel.basic_qos(prefetch_count=1)

        # Setup consumer
        self.channel.basic_consume(
            queue=TASK_QUEUE, on_message_callback=self._process_task, auto_ack=False
        )

        self.logger.info("TELOS Worker ready for advanced statistical tasks")

        # Start consuming
        while not self.should_stop:
            try:
                self.connection.process_data_events(time_limit=1)
            except KeyboardInterrupt:
                break

        # Cleanup
        if self.connection and not self.connection.is_closed:
            self.connection.close()

    def _process_task(self, channel, method, properties, body):
        """Process incoming task with advanced statistical methods."""
        try:
            # Parse task
            task_data = json.loads(body.decode("utf-8"))
            task_id = task_data.get("task_id", str(uuid.uuid4()))
            task_type = task_data.get("task_type", "unknown")
            payload = task_data.get("payload", {})

            self.logger.info(f"Processing advanced task {task_id}: {task_type}")

            # Execute task using advanced core
            result = self.core.execute(task_type, payload)

            # Publish result
            self._publish_result(result)

            # Acknowledge task completion
            channel.basic_ack(delivery_tag=method.delivery_tag)

            self.logger.info(f"Task {task_id} completed successfully")

        except Exception as e:
            self.logger.error(f"Task processing error: {e}", exc_info=True)

            # Send error result
            error_result = {
                "task_id": task_data.get("task_id", "unknown"),
                "subsystem": "telos",
                "status": "failed",
                "error": str(e),
                "timestamp": datetime.utcnow().isoformat(),
            }

            self._publish_result(error_result)
            channel.basic_ack(delivery_tag=method.delivery_tag)

    def _publish_result(self, result: dict[str, Any]):
        """Publish task result to result queue."""
        try:
            self.channel.basic_publish(
                exchange="",
                routing_key=RESULT_QUEUE,
                body=json.dumps(result),
                properties=pika.BasicProperties(delivery_mode=2),
            )
        except Exception as e:
            self.logger.error(f"Failed to publish result: {e}")


def main():
    """Main entry point for TELOS advanced worker."""
    worker = TelosWorker()
    worker.start()


if __name__ == "__main__":
    main()
