"""
LOGOS PXL Core API Gateway
Provides authentication, rate limiting, provenance headers, and request routing
"""

import os
import time
import yaml
import structlog
from typing import Dict, Any, Optional
from datetime import datetime, timedelta

import uvicorn
from fastapi import FastAPI, Request, Response, HTTPException, Depends
from fastapi.middleware.cors import CORSMiddleware
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials
from pydantic import BaseModel
from jose import jwt, JWTError
from slowapi import Limiter, _rate_limit_exceeded_handler
from slowapi.util import get_remote_address
from slowapi.errors import RateLimitExceeded
from slowapi.middleware import SlowAPIMiddleware
import httpx
from prometheus_client import Counter, Histogram, generate_latest, CONTENT_TYPE_LATEST

# Configure structured logging
structlog.configure(
    processors=[
        structlog.stdlib.filter_by_level,
        structlog.stdlib.add_logger_name,
        structlog.stdlib.add_log_level,
        structlog.stdlib.PositionalArgumentsFormatter(),
        structlog.processors.TimeStamper(fmt="iso"),
        structlog.processors.StackInfoRenderer(),
        structlog.processors.format_exc_info,
        structlog.processors.UnicodeDecoder(),
        structlog.processors.JSONRenderer()
    ],
    context_class=dict,
    logger_factory=structlog.stdlib.LoggerFactory(),
    wrapper_class=structlog.stdlib.BoundLogger,
    cache_logger_on_first_use=True,
)

logger = structlog.get_logger()

# Load configuration
with open('config.yaml', 'r') as f:
    config = yaml.safe_load(f)

# Initialize FastAPI app
app = FastAPI(
    title="LOGOS PXL Core API Gateway",
    version="1.0.0",
    description="Coq-verified proof and overlay services"
)

# Configure CORS
app.add_middleware(
    CORSMiddleware,
    allow_origins=config['cors']['allow_origins'],
    allow_credentials=config['cors']['allow_credentials'],
    allow_methods=config['cors']['allow_methods'],
    allow_headers=config['cors']['allow_headers'],
)

# Configure rate limiting
limiter = Limiter(key_func=get_remote_address)
app.state.limiter = limiter
app.add_exception_handler(RateLimitExceeded, _rate_limit_exceeded_handler)
app.add_middleware(SlowAPIMiddleware)

# JWT Configuration
JWT_SECRET = os.getenv('JWT_SECRET_KEY', 'development-secret-key')
JWT_ALGORITHM = config['auth']['algorithm']
security = HTTPBearer(auto_error=False)

# Metrics
REQUEST_COUNT = Counter('gateway_requests_total', 'Total requests', ['method', 'endpoint', 'status'])
REQUEST_LATENCY = Histogram('gateway_request_duration_seconds', 'Request latency', ['method', 'endpoint'])

# Provenance data (would be loaded from build artifacts in production)
PROVENANCE_DATA = {
    'coqchk_stamp': os.getenv('COQCHK_STAMP', 'development-stamp'),
    'build_sha': os.getenv('BUILD_SHA', 'development-sha'),
    'v4_sha': os.getenv('V4_SHA', 'development-v4-sha'),
}

class HealthResponse(BaseModel):
    status: str
    version: str
    coqchk_stamp: str
    build_sha: str
    v4_sha: str

async def verify_token(credentials: Optional[HTTPAuthorizationCredentials] = Depends(security)):
    """Verify JWT token for authenticated endpoints"""
    if not config['auth']['enabled']:
        return None

    if not credentials:
        raise HTTPException(status_code=401, detail="Authentication required")

    try:
        payload = jwt.decode(credentials.credentials, JWT_SECRET, algorithms=[JWT_ALGORITHM])
        return payload
    except JWTError:
        raise HTTPException(status_code=401, detail="Invalid token")

@app.get("/v1/health", response_model=HealthResponse)
async def health_check():
    """Health check endpoint with provenance data"""
    return HealthResponse(
        status="healthy",
        version="1.0.0",
        coqchk_stamp=PROVENANCE_DATA['coqchk_stamp'],
        build_sha=PROVENANCE_DATA['build_sha'],
        v4_sha=PROVENANCE_DATA['v4_sha']
    )

@app.get("/metrics")
async def metrics():
    """Prometheus metrics endpoint"""
    return Response(
        content=generate_latest(),
        media_type=CONTENT_TYPE_LATEST
    )

async def proxy_request(service_name: str, path: str, request: Request) -> Response:
    """Proxy request to upstream service"""
    service_config = config['services'][service_name]
    service_url = f"{service_config['url']}{path}"

    # Prepare headers
    headers = dict(request.headers)
    # Remove hop-by-hop headers
    headers.pop('host', None)
    headers.pop('connection', None)

    # Add provenance headers
    if config['provenance']['coqchk_stamp']:
        headers['X-PXL-Coqchk'] = PROVENANCE_DATA['coqchk_stamp']
    if config['provenance']['build_sha']:
        headers['X-Build-SHA'] = PROVENANCE_DATA['build_sha']
    if config['provenance']['v4_sha']:
        headers['X-V4-SHA'] = PROVENANCE_DATA['v4_sha']

    async with httpx.AsyncClient(timeout=service_config['timeout_seconds']) as client:
        start_time = time.time()

        try:
            response = await client.request(
                method=request.method,
                url=service_url,
                headers=headers,
                content=await request.body(),
                params=request.query_params,
            )

            latency = time.time() - start_time

            # Record metrics
            REQUEST_COUNT.labels(
                method=request.method,
                endpoint=path,
                status=response.status_code
            ).inc()

            REQUEST_LATENCY.labels(
                method=request.method,
                endpoint=path
            ).observe(latency)

            # Log request
            logger.info(
                "proxied_request",
                method=request.method,
                path=path,
                service=service_name,
                status=response.status_code,
                latency=latency
            )

            # Return response
            return Response(
                content=response.content,
                status_code=response.status_code,
                headers=dict(response.headers)
            )

        except httpx.TimeoutException:
            REQUEST_COUNT.labels(method=request.method, endpoint=path, status=504).inc()
            raise HTTPException(status_code=504, detail="Service timeout")
        except Exception as e:
            REQUEST_COUNT.labels(method=request.method, endpoint=path, status=502).inc()
            logger.error("proxy_error", service=service_name, path=path, error=str(e))
            raise HTTPException(status_code=502, detail="Service unavailable")

# Route handlers
@app.api_route("/v1/proofs", methods=["POST"])
@limiter.limit(f"{config['rate_limit']['max_requests']}/minute")
async def proofs(request: Request, token: Optional[dict] = Depends(verify_token)):
    return await proxy_request('pxl_core', '/v1/proofs', request)

@app.api_route("/v1/proofs/{proof_id}", methods=["GET"])
@limiter.limit(f"{config['rate_limit']['max_requests']}/minute")
async def get_proof(proof_id: str, request: Request):
    return await proxy_request('pxl_core', f'/v1/proofs/{proof_id}', request)

@app.api_route("/v1/overlays/chrono", methods=["POST"])
@limiter.limit(f"{config['rate_limit']['max_requests']}/minute")
async def chrono_overlay(request: Request, token: Optional[dict] = Depends(verify_token)):
    return await proxy_request('overlay_chrono', '/v1/overlays/chrono', request)

@app.api_route("/v1/overlays/v4", methods=["POST"])
@limiter.limit(f"{config['rate_limit']['max_requests']}/minute")
async def v4_overlay(request: Request, token: Optional[dict] = Depends(verify_token)):
    return await proxy_request('overlay_v4', '/v1/overlays/v4', request)

@app.api_route("/v1/metrics", methods=["GET"])
async def metrics_proxy(request: Request):
    return await proxy_request('pxl_core', '/v1/metrics', request)

if __name__ == "__main__":
    uvicorn.run(
        "gateway:app",
        host=config['server']['host'],
        port=config['server']['port'],
        reload=False,
        log_level=config['monitoring']['log_level']
    )