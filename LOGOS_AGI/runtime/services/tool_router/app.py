"""
FastAPI Tool Router with:
- Request schemas
- Request ID + structured JSON logs
- Optional HMAC signing
- Rate limiting (memory or Redis)
- Prometheus metrics
- Retries with jitter
- Per-tool circuit breaker
"""
from __future__ import annotations

import hashlib
import hmac
import json
import logging
import os
import random
import time
import typing as t
import uuid
from dataclasses import dataclass

import requests
from fastapi import FastAPI, Header, HTTPException, Request, status
from fastapi.responses import JSONResponse, PlainTextResponse
from prometheus_client import (
    CONTENT_TYPE_LATEST,
    CollectorRegistry,
    Counter,
    Histogram,
    generate_latest,
)
from pydantic import BaseModel, Field, ValidationError, field_validator

# -------- Config --------
WEB_URL = os.getenv("WEB_URL", "http://web:8000")
DB_URL = os.getenv("DB_URL", "http://db:8000")
FS_URL = os.getenv("FS_URL", "http://fs:8000")
CRAWL_URL = os.getenv("CRAWL_URL", "http://crawl:8000")
TETRAGNOS_URL = os.getenv("TETRAGNOS_URL", "http://tetragnos:8000")
TELOS_URL = os.getenv("TELOS_URL", "http://telos:8000")
THONOC_URL = os.getenv("THONOC_URL", "http://thonoc:8000")

RATE_LIMIT_REQS = int(os.getenv("RATE_LIMIT_REQS", "100"))
RATE_LIMIT_WINDOW_SECS = int(os.getenv("RATE_LIMIT_WINDOW_SECS", "60"))
USE_REDIS = os.getenv("USE_REDIS_RATE_LIMIT", "false").lower() == "true"
REDIS_URL = os.getenv("REDIS_URL", "redis://redis:6379/0")

SIGNING_SECRET = os.getenv("SIGNING_SECRET", "")
MAX_SKEW_SECS = int(os.getenv("SIGNING_MAX_SKEW_SECS", "300"))

RETRY_MAX_ATTEMPTS = int(os.getenv("RETRY_MAX_ATTEMPTS", "3"))
RETRY_BASE_SECS = float(os.getenv("RETRY_BASE_SECS", "0.2"))
RETRY_JITTER_SECS = float(os.getenv("RETRY_JITTER_SECS", "0.2"))

CB_FAIL_THRESHOLD = int(os.getenv("CB_FAIL_THRESHOLD", "5"))
CB_COOLDOWN_SECS = int(os.getenv("CB_COOLDOWN_SECS", "30"))

TIMEOUT_SECS = float(os.getenv("UPSTREAM_TIMEOUT_SECS", "30"))

ALLOWED_TOOLS: dict[str, str] = {
    "web": WEB_URL,
    "db": DB_URL,
    "fs": FS_URL,
    "crawl": CRAWL_URL,
    "tetragnos": TETRAGNOS_URL,
    "telos": TELOS_URL,
    "thonoc": THONOC_URL,
}

# -------- Logging --------
class JsonFormatter(logging.Formatter):
    def format(self, record: logging.LogRecord) -> str:  # why: consistent machine-readable logs
        payload = {
            "ts": int(time.time()),
            "level": record.levelname,
            "msg": record.getMessage(),
        }
        # optional extras
        for k in ("request_id", "path", "method", "status"):
            if hasattr(record, k):
                payload[k] = getattr(record, k)
        return json.dumps(payload, ensure_ascii=False)

logger = logging.getLogger("tool_router")
if not logger.handlers:
    h = logging.StreamHandler()
    h.setFormatter(JsonFormatter())
    logger.addHandler(h)
logger.setLevel(logging.INFO)

# -------- Metrics --------
_registry = CollectorRegistry()
MET_REQS = Counter("router_requests_total", "Total requests", ["endpoint", "method", "status"], registry=_registry)
MET_RATELIMIT = Counter("router_rate_limited_total", "Rate limited requests", ["reason"], registry=_registry)
MET_UPSTREAM = Histogram("router_upstream_latency_seconds", "Upstream latency", ["tool", "result"], registry=_registry)
MET_CB_STATE = Counter("router_circuit_open_total", "Circuit opened events", ["tool"], registry=_registry)

# -------- Schemas --------
class ProofToken(BaseModel):
    token: str = Field(..., min_length=1)

class RouteArgs(BaseModel):
    model_config = {"extra": "allow"}

class RouteRequest(BaseModel):
    tool: str
    args: RouteArgs
    proof_token: ProofToken

    @field_validator("tool")
    @classmethod
    def _tool_supported(cls, v: str) -> str:
        if v not in ALLOWED_TOOLS:
            raise ValueError(f"unsupported tool '{v}'")
        return v

class ToolResponse(BaseModel):
    ok: bool
    tool: str | None = None
    data: dict[str, t.Any] | None = None
    error: str | None = None

# -------- Rate limiting --------
# redis is optional and injected lazily for easy testing
_redis = None
if USE_REDIS:
    try:
        import redis  # type: ignore
        _redis = redis.Redis.from_url(REDIS_URL, decode_responses=True)
        _redis.ping()
    except Exception as e:
        logger.error("Redis disabled: %s", e)

@dataclass
class Bucket:
    reset_at: float
    count: int

_buckets: dict[str, Bucket] = {}

def _bucket_key(req: Request, api_key: str | None) -> str:
    if api_key:
        return f"k:{api_key}"
    ip = req.client.host if req.client else "unknown"
    return f"ip:{ip}"

def _check_rate_limit_memory(key: str) -> tuple[bool, int]:
    now = time.time()
    window = RATE_LIMIT_WINDOW_SECS
    limit = RATE_LIMIT_REQS
    b = _buckets.get(key)
    if not b or now >= b.reset_at:
        _buckets[key] = Bucket(reset_at=now + window, count=1)
        return True, int(_buckets[key].reset_at - now)
    if b.count < limit:
        b.count += 1
        return True, int(b.reset_at - now)
    return False, int(b.reset_at - now)

def _check_rate_limit_redis(key: str) -> tuple[bool, int]:
    assert _redis is not None
    now = int(time.time())
    window = RATE_LIMIT_WINDOW_SECS
    limit = RATE_LIMIT_REQS
    win_start = now - (now % window)
    rk = f"rl:{key}:{win_start}"
    pipe = _redis.pipeline()
    pipe.incr(rk, 1)
    pipe.expire(rk, window)
    current, _ = pipe.execute()
    retry = window - (now - win_start)
    return (int(current) <= limit, retry)

def _check_rate_limit(req: Request, api_key: str | None) -> tuple[bool, int]:
    key = _bucket_key(req, api_key)
    if _redis:
        return _check_rate_limit_redis(key)
    return _check_rate_limit_memory(key)

# -------- Circuit breaker --------
@dataclass
class Breaker:
    failures: int = 0
    open_until: float = 0.0
    half_open: bool = False

_breakers: dict[str, Breaker] = {tool: Breaker() for tool in ALLOWED_TOOLS}

def _cb_can_call(tool: str) -> bool:
    b = _breakers[tool]
    now = time.time()
    if b.open_until > now:
        return False
    if b.open_until and now >= b.open_until:
        b.half_open = True
    return True

def _cb_record_success(tool: str) -> None:
    _breakers[tool] = Breaker()

def _cb_record_failure(tool: str) -> None:
    b = _breakers[tool]
    b.failures += 1
    if b.failures >= CB_FAIL_THRESHOLD:
        b.open_until = time.time() + CB_COOLDOWN_SECS
        b.half_open = False
        MET_CB_STATE.labels(tool=tool).inc()

# -------- HMAC --------
def _valid_signature(ts: str, sig: str, body: bytes) -> bool:
    try:
        ts_int = int(ts)
    except Exception:
        return False
    now = int(time.time())
    if abs(now - ts_int) > MAX_SKEW_SECS:
        return False
    body_str = body.decode('utf-8', 'ignore')
    msg = f"{ts}.{body_str}".encode()
    digest = hmac.new(SIGNING_SECRET.encode(), msg, hashlib.sha256).hexdigest()
    return hmac.compare_digest(digest, sig.lower())

# -------- App --------
app = FastAPI(title="LOGOS Tool Router", version="2.0.0")

@app.middleware("http")
async def core_middleware(request: Request, call_next):
    # request id
    req_id = request.headers.get("X-Request-ID") or str(uuid.uuid4())
    # rate limit
    api_key = request.headers.get("X-API-Key")
    allowed, retry_in = _check_rate_limit(request, api_key)
    if not allowed:
        MET_RATELIMIT.labels(reason="limit").inc()
        MET_REQS.labels(endpoint=request.url.path, method=request.method, status="429").inc()
        return JSONResponse(
            {"ok": False, "error": "rate_limited"},
            status_code=status.HTTP_429_TOO_MANY_REQUESTS,
            headers={"Retry-After": str(max(1, retry_in)), "X-Request-ID": req_id},
        )
    # HMAC for POST /route when enabled
    if SIGNING_SECRET and request.url.path == "/route" and request.method == "POST":
        ts = request.headers.get("X-Timestamp", "")
        sig = request.headers.get("X-Signature", "").lower()
        body = await request.body()
        request._body = body
        if not ts or not sig or not _valid_signature(ts, sig, body):
            MET_REQS.labels(endpoint="/route", method="POST", status="401").inc()
            return JSONResponse(
                {"ok": False, "error": "invalid_signature"},
                status_code=status.HTTP_401_UNAUTHORIZED,
                headers={"X-Request-ID": req_id},
            )
    resp = await call_next(request)
    resp.headers["X-Request-ID"] = req_id
    # structured access log
    rec = logger.makeRecord(logger.name, logging.INFO, "", 0, "access", args=(), exc_info=None)
    rec.request_id = req_id
    rec.path = request.url.path
    rec.method = request.method
    rec.status = getattr(resp, "status_code", 0)
    logger.handle(rec)
    MET_REQS.labels(endpoint=request.url.path, method=request.method, status=str(getattr(resp, "status_code", 0))).inc()
    return resp

@app.exception_handler(ValidationError)
async def pydantic_handler(_: Request, exc: ValidationError):
    return JSONResponse(
        status_code=status.HTTP_422_UNPROCESSABLE_ENTITY,
        content={"ok": False, "error": "validation_error", "details": exc.errors()},
    )

@app.get("/health")
def health():
    mode = "redis" if _redis else "memory"
    return {
        "ok": True,
        "rate_limit": {"limit": RATE_LIMIT_REQS, "window_secs": RATE_LIMIT_WINDOW_SECS, "backend": mode},
        "signing": bool(SIGNING_SECRET),
        "circuit": {"threshold": CB_FAIL_THRESHOLD, "cooldown_secs": CB_COOLDOWN_SECS},
    }

@app.get("/metrics")
def metrics():
    return PlainTextResponse(generate_latest(_registry), media_type=CONTENT_TYPE_LATEST)

# -------- Upstream call with retries + breaker --------
def _post_with_retries(tool: str, url: str, payload: dict, request_id: str) -> requests.Response:
    if not _cb_can_call(tool):
        raise HTTPException(status_code=503, detail=f"circuit_open:{tool}")
    attempt = 0
    last_exc: Exception | None = None
    start = time.time()
    while attempt < RETRY_MAX_ATTEMPTS:
        attempt += 1
        try:
            return requests.post(
                url,
                json=payload,
                headers={"X-Request-ID": request_id},
                timeout=TIMEOUT_SECS,
            )
        except requests.RequestException as e:
            last_exc = e
            _cb_record_failure(tool)
            if attempt >= RETRY_MAX_ATTEMPTS:
                MET_UPSTREAM.labels(tool=tool, result="error").observe(time.time() - start)
                raise HTTPException(status_code=502, detail=f"upstream_error:{e}")
            sleep = (RETRY_BASE_SECS * (2 ** (attempt - 1))) + random.uniform(0, RETRY_JITTER_SECS)
            time.sleep(min(sleep, 5.0))
    # should not reach
    raise HTTPException(status_code=502, detail=f"upstream_error:{last_exc}")

@app.post("/route", response_model=ToolResponse)
def route(req: RouteRequest, request: Request, x_api_key: str | None = Header(default=None)):
    base = ALLOWED_TOOLS[req.tool]
    url = f"{base}/invoke"
    request_id = request.headers.get("X-Request-ID", str(uuid.uuid4()))
    payload = {"args": req.args.model_dump(), "proof_token": req.proof_token.model_dump()}
    t0 = time.time()
    r = _post_with_retries(req.tool, url, payload, request_id)
    elapsed = time.time() - t0
    if r.status_code >= 400:
        MET_UPSTREAM.labels(tool=req.tool, result="bad").observe(elapsed)
        _cb_record_failure(req.tool)
        return ToolResponse(ok=False, tool=req.tool, error=f"upstream_{r.status_code}", data=_safe_json(r))
    MET_UPSTREAM.labels(tool=req.tool, result="ok").observe(elapsed)
    _cb_record_success(req.tool)
    return ToolResponse(ok=True, tool=req.tool, data=_safe_json(r))

def _safe_json(resp: requests.Response) -> dict[str, t.Any]:
    try:
        data = resp.json()
        return data if isinstance(data, dict) else {"raw": data}
    except Exception:
        return {"raw": resp.text}


if __name__ == "__main__":
    import uvicorn

    print("🔧 Starting LOGOS Tool Router")
    print(f"   Rate Limit: {RATE_LIMIT_REQS} req/{RATE_LIMIT_WINDOW_SECS}s")
    print(f"   Tools:      {list(ALLOWED_TOOLS.keys())}")
    uvicorn.run(app, host="0.0.0.0", port=8071)
