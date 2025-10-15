from typing import Any

from fastapi import FastAPI, HTTPException
from pydantic import BaseModel

app = FastAPI()


class Invoke(BaseModel):
    tool: str
    args: dict[str, Any]
    proof_token: dict[str, Any]


@app.get("/health")
def health():
    return {"ok": True, "subsystem": "TELOS"}


def simple_linear_forecast(series: list[float], horizon: int) -> list[float]:
    """Simple linear extrapolation forecast"""
    if len(series) < 2:
        return [series[-1]] * horizon if series else [0.0] * horizon

    # Simple linear trend calculation
    n = len(series)
    x = list(range(n))
    y = series

    # Calculate slope and intercept
    sum_x = sum(x)
    sum_y = sum(y)
    sum_xy = sum(x[i] * y[i] for i in range(n))
    sum_x2 = sum(x[i] * x[i] for i in range(n))

    slope = (n * sum_xy - sum_x * sum_y) / (n * sum_x2 - sum_x * sum_x)
    intercept = (sum_y - slope * sum_x) / n

    # Generate forecast
    forecast = []
    for i in range(horizon):
        future_x = n + i
        forecast_value = intercept + slope * future_x
        forecast.append(forecast_value)

    return forecast


@app.post("/invoke")
def invoke(t: Invoke):
    if not t.proof_token or "kernel_hash" not in t.proof_token:
        raise HTTPException(403, "missing proof token")
    if t.tool != "telos":
        raise HTTPException(400, "bad tool route")

    op = t.args.get("op")
    if op == "forecast_series":
        series: list[float] = t.args.get("series") or []
        if not series or len(series) < 2:
            raise HTTPException(400, "series[] length >= 2 required")
        horizon = int(t.args.get("horizon") or 6)
        try:
            forecast = simple_linear_forecast(series, horizon)
            return {"ok": True, "op": "forecast_series", "horizon": horizon, "forecast": forecast}
        except Exception as e:
            raise HTTPException(500, f"forecast failed: {e}")

    raise HTTPException(400, "unsupported op")
