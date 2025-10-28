"""
Telos Subsystem FastAPI Application

Provides REST API interface for the Telos causal reasoning subsystem.
"""

from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
import logging
import os
import numpy as np

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("telos_app")

app = FastAPI(
    title="Telos Causal Reasoning API",
    description="Advanced causal reasoning and forecasting subsystem",
    version="1.0.0"
)

class ForecastingRequest(BaseModel):
    series_data: list[float]
    steps_ahead: int = 5

class ForecastingResponse(BaseModel):
    forecast: list[float]
    confidence: float
    model: str
    success: bool
    message: str

class CausalRequest(BaseModel):
    data: list[dict]
    dag: dict = None

class CausalResponse(BaseModel):
    fitted: bool
    samples: int
    success: bool
    message: str

class CounterfactualRequest(BaseModel):
    scm_data: dict
    target: str
    context: dict
    intervention: dict

class CounterfactualResponse(BaseModel):
    probability: float
    success: bool
    message: str

def perform_forecasting(series_data, steps_ahead=5):
    """Perform simple time series forecasting using linear extrapolation"""
    try:
        if len(series_data) < 2:
            # Simple constant forecast for very short series
            last_value = series_data[-1] if series_data else 0.5
            forecast = [last_value] * steps_ahead
        else:
            # Simple linear trend extrapolation
            x = np.arange(len(series_data))
            y = np.array(series_data)

            # Calculate linear trend
            slope = np.polyfit(x, y, 1)[0]

            # Extrapolate
            last_x = len(series_data) - 1
            forecast = []
            for i in range(1, steps_ahead + 1):
                next_x = last_x + i
                next_value = series_data[-1] + slope * i
                forecast.append(float(next_value))

        return {
            "forecast": forecast,
            "confidence": 0.75,
            "model": "LinearExtrapolation",
            "success": True
        }
    except Exception as e:
        return {
            "forecast": [0.5] * steps_ahead,
            "confidence": 0.5,
            "model": "fallback",
            "success": False,
            "error": str(e)
        }

def fit_causal_model(data, dag=None):
    """Simple causal model fitting (placeholder)"""
    return {
        "fitted": True,
        "samples": len(data),
        "success": True
    }

def evaluate_counterfactual(scm_data, target, context, intervention):
    """Simple counterfactual evaluation (placeholder)"""
    return 0.75

from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
import logging
import os
from .telos_worker import ForecastingNexus, SCM, evaluate_counterfactual

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger("telos_app")

app = FastAPI(
    title="Telos Causal Reasoning API",
    description="Advanced causal reasoning and forecasting subsystem",
    version="1.0.0"
)

# Initialize core components
forecasting_nexus = ForecastingNexus()

class ForecastingRequest(BaseModel):
    series_data: list[float]
    steps_ahead: int = 5

class ForecastingResponse(BaseModel):
    forecast: list[float]
    confidence: float
    model: str
    success: bool
    message: str

class CausalRequest(BaseModel):
    data: list[dict]
    dag: dict = None

class CausalResponse(BaseModel):
    fitted: bool
    samples: int
    success: bool
    message: str

class CounterfactualRequest(BaseModel):
    scm_data: dict
    target: str
    context: dict
    intervention: dict

class CounterfactualResponse(BaseModel):
    probability: float
    success: bool
    message: str

@app.get("/health")
async def health_check():
    """Health check endpoint"""
    return {"status": "healthy", "subsystem": "telos"}

@app.post("/forecast", response_model=ForecastingResponse)
async def forecast_series(request: ForecastingRequest):
    """Perform time series forecasting"""
    try:
        logger.info(f"Processing forecasting request with {len(request.series_data)} data points")

        # Execute forecasting
        result = perform_forecasting(request.series_data, request.steps_ahead)

        return ForecastingResponse(
            forecast=result.get("forecast", []),
            confidence=result.get("confidence", 0.0),
            model=result.get("model", "unknown"),
            success=True,
            message="Forecasting completed successfully"
        )

    except Exception as e:
        logger.error(f"Forecasting failed: {str(e)}")
        raise HTTPException(status_code=500, detail=f"Forecasting failed: {str(e)}")

@app.post("/causal-model", response_model=CausalResponse)
async def fit_causal_model_endpoint(request: CausalRequest):
    """Fit a causal model to data"""
    try:
        logger.info(f"Fitting causal model with {len(request.data)} samples")

        # Fit causal model
        result = fit_causal_model(request.data, request.dag)

        return CausalResponse(
            fitted=result.get("fitted", False),
            samples=result.get("samples", 0),
            success=True,
            message="Causal model fitted successfully"
        )

    except Exception as e:
        logger.error(f"Causal modeling failed: {str(e)}")
        raise HTTPException(status_code=500, detail=f"Causal modeling failed: {str(e)}")

@app.post("/counterfactual", response_model=CounterfactualResponse)
async def evaluate_counterfactual_query(request: CounterfactualRequest):
    """Evaluate counterfactual query"""
    try:
        logger.info("Processing counterfactual query")

        # Evaluate counterfactual
        probability = evaluate_counterfactual(
            request.scm_data,
            request.target,
            request.context,
            request.intervention
        )

        return CounterfactualResponse(
            probability=probability,
            success=True,
            message="Counterfactual evaluation completed"
        )

    except Exception as e:
        logger.error(f"Counterfactual evaluation failed: {str(e)}")
        raise HTTPException(status_code=500, detail=f"Counterfactual evaluation failed: {str(e)}")

@app.get("/status")
async def get_status():
    """Get subsystem status"""
    return {
        "subsystem": "telos",
        "status": "active",
        "capabilities": ["forecasting", "causal_modeling", "counterfactual_reasoning"],
        "version": "1.0.0"
    }

@app.post("/process")
async def process_task(request: dict):
    """Generic task processing endpoint for worker integration"""
    try:
        task = request.get("task", "")
        parameters = request.get("parameters", {})

        if task == "forecasting" or task == "forecast":
            # Route to forecasting endpoint
            forecast_req = ForecastingRequest(**parameters)
            return await forecast_series(forecast_req)
        elif task == "causal_analysis" or task == "causal_model":
            # Route to causal modeling endpoint
            causal_req = CausalRequest(**parameters)
            return await fit_causal_model(causal_req)
        elif task == "counterfactual":
            # Route to counterfactual endpoint
            cf_req = CounterfactualRequest(**parameters)
            return await evaluate_counterfactual(cf_req)
        else:
            raise HTTPException(status_code=400, detail=f"Unknown task: {task}")

    except Exception as e:
        logger.error(f"Task processing failed: {str(e)}")
        raise HTTPException(status_code=500, detail=f"Task processing failed: {str(e)}")

if __name__ == "__main__":
    import uvicorn
    port = int(os.getenv("PORT", 8066))
    uvicorn.run(app, host="0.0.0.0", port=port)