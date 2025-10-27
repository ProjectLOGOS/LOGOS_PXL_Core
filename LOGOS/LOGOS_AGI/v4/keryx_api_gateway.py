# logos_agi_v2/services/keryx_api/gateway_service.py

"""Keryx API Gateway - External Request Interface

REST API gateway providing secure external access to LOGOS AGI system.
Routes all requests through Logos Nexus for Trinity-grounded validation.

Critical Safety Feature:
- All requests route to logos_nexus_requests queue
- No direct worker access permitted
- Comprehensive input validation

Dependencies: fastapi, pika, uuid, logging
"""

import os
import json
import uuid
import logging
from typing import Dict, Any, Optional
from datetime import datetime

from fastapi import FastAPI, HTTPException, Request
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse
from pydantic import BaseModel, Field
import pika
import uvicorn

# Configuration
SERVICE_NAME = "KERYX_API"
API_HOST = os.getenv("API_HOST", "0.0.0.0")
API_PORT = int(os.getenv("API_PORT", "5000"))
RABBITMQ_HOST = os.getenv("RABBITMQ_HOST", "rabbitmq")
RABBITMQ_PORT = int(os.getenv("RABBITMQ_PORT", "5672"))

# Queue configuration - CRITICAL SAFETY REQUIREMENT
LOGOS_NEXUS_REQUESTS = "logos_nexus_requests"

# Logging setup
logging.basicConfig(
    level=logging.INFO, format=f"%(asctime)s - %(levelname)s - {SERVICE_NAME} - %(message)s"
)
logger = logging.getLogger(SERVICE_NAME)


# Request models
class GoalSubmission(BaseModel):
    """External goal submission request model."""

    content: str = Field(..., min_length=1, max_length=2000, description="Goal description")
    type: str = Field(default="query", description="Request type classification")
    context: Dict[str, Any] = Field(default_factory=dict, description="Additional context")
    requester_id: Optional[str] = Field(default=None, description="Requester identification")


class APIResponse(BaseModel):
    """Standard API response model."""

    status: str
    message: str
    task_id: Optional[str] = None
    timestamp: str
    data: Optional[Dict[str, Any]] = None


# FastAPI application
app = FastAPI(
    title="LOGOS AGI Keryx Gateway",
    description="External API gateway for LOGOS AGI system",
    version="2.0.0",
    docs_url="/docs",
    redoc_url="/redoc",
)

# CORS configuration
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  # Configure appropriately for production
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)


class MessageBroker:
    """RabbitMQ connection manager for request routing."""

    def __init__(self):
        self.connection = None
        self.channel = None
        self.connect()

    def connect(self):
        """Establish RabbitMQ connection."""
        try:
            self.connection = pika.BlockingConnection(
                pika.ConnectionParameters(host=RABBITMQ_HOST, port=RABBITMQ_PORT, heartbeat=600)
            )
            self.channel = self.connection.channel()

            # Declare target queue
            self.channel.queue_declare(queue=LOGOS_NEXUS_REQUESTS, durable=True)

            logger.info("Message broker connected")

        except Exception as e:
            logger.error(f"Message broker connection failed: {e}")
            raise

    def publish_request(self, request_data: Dict[str, Any]) -> bool:
        """Publish request to Logos Nexus for safety validation.

        Args:
            request_data: Request payload for processing

        Returns:
            True if publication successful, False otherwise
        """
        try:
            if not self.connection or self.connection.is_closed:
                self.connect()

            self.channel.basic_publish(
                exchange="",
                routing_key=LOGOS_NEXUS_REQUESTS,
                body=json.dumps(request_data),
                properties=pika.BasicProperties(
                    delivery_mode=2,  # Persistent message
                    correlation_id=request_data.get("request_id"),
                ),
            )

            logger.info(f"Request {request_data['request_id']} published to Logos Nexus")
            return True

        except Exception as e:
            logger.error(f"Request publication failed: {e}")
            return False

    def close(self):
        """Close message broker connection."""
        if self.connection and not self.connection.is_closed:
            self.connection.close()


# Global message broker instance
broker = MessageBroker()


@app.on_event("startup")
async def startup_event():
    """Initialize API gateway on startup."""
    logger.info("Keryx API Gateway starting...")


@app.on_event("shutdown")
async def shutdown_event():
    """Clean up resources on shutdown."""
    logger.info("Keryx API Gateway shutting down...")
    broker.close()


@app.get("/health")
async def health_check():
    """Health check endpoint for monitoring."""
    return APIResponse(
        status="healthy",
        message="Keryx API Gateway operational",
        timestamp=datetime.utcnow().isoformat(),
        data={
            "service": SERVICE_NAME,
            "version": "2.0.0",
            "broker_connected": broker.connection and not broker.connection.is_closed,
        },
    )


@app.get("/status")
async def system_status():
    """System status endpoint for operational monitoring."""
    return APIResponse(
        status="operational",
        message="System status retrieved",
        timestamp=datetime.utcnow().isoformat(),
        data={
            "gateway_status": "active",
            "message_broker": "connected"
            if broker.connection and not broker.connection.is_closed
            else "disconnected",
            "target_queue": LOGOS_NEXUS_REQUESTS,
            "safety_routing": "enabled",
        },
    )


@app.post("/submit_goal")
async def submit_goal(goal: GoalSubmission, request: Request):
    """Submit goal for processing through LOGOS AGI system.

    Critical Safety Implementation:
    - Routes ALL requests to logos_nexus_requests queue
    - Ensures Trinity-grounded validation via Logos Nexus
    - No direct worker access permitted

    Args:
        goal: Goal submission with content and metadata
        request: FastAPI request context

    Returns:
        202 Accepted response with task tracking ID
    """
    try:
        # Generate unique request identifier
        task_id = f"req_{uuid.uuid4().hex[:12]}"

        # Extract client information
        client_ip = request.client.host if request.client else "unknown"

        # Construct request payload for Logos Nexus
        request_payload = {
            "request_id": task_id,
            "content": goal.content,
            "type": goal.type,
            "context": {
                **goal.context,
                "client_ip": client_ip,
                "api_gateway": SERVICE_NAME,
                "submission_time": datetime.utcnow().isoformat(),
            },
            "requester_id": goal.requester_id or f"api_user_{client_ip}",
            "timestamp": datetime.utcnow().isoformat(),
        }

        # CRITICAL: Route to Logos Nexus for safety validation
        publication_success = broker.publish_request(request_payload)

        if not publication_success:
            raise HTTPException(
                status_code=503, detail="Service temporarily unavailable - message broker error"
            )

        # Return fire-and-forget acknowledgment
        return JSONResponse(
            status_code=202,
            content={
                "status": "accepted",
                "message": "Goal submitted for processing",
                "task_id": task_id,
                "timestamp": datetime.utcnow().isoformat(),
                "note": "Request routed through safety validation pipeline",
            },
        )

    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Goal submission error: {e}")
        raise HTTPException(status_code=500, detail=f"Internal server error: {str(e)}")


@app.post("/submit_query")
async def submit_query(goal: GoalSubmission, request: Request):
    """Submit query for analysis (alias for submit_goal with query type).

    Args:
        goal: Query submission with content and metadata
        request: FastAPI request context

    Returns:
        202 Accepted response with task tracking ID
    """
    # Force type to query
    goal.type = "query"
    return await submit_goal(goal, request)


@app.get("/info")
async def system_info():
    """System information endpoint."""
    return APIResponse(
        status="info",
        message="LOGOS AGI system information",
        timestamp=datetime.utcnow().isoformat(),
        data={
            "system_name": "LOGOS AGI v2.0",
            "description": "Trinity-grounded Artificial General Intelligence",
            "api_version": "2.0.0",
            "safety_features": [
                "Trinity-grounded validation",
                "Formal system verification",
                "Principle-based authorization",
                "Comprehensive audit logging",
            ],
            "submission_flow": [
                "External request received",
                "Routed to Logos Nexus",
                "Safety validation applied",
                "Workflow planning initiated",
                "Distributed execution",
                "Result synthesis",
            ],
        },
    )


# Error handlers
@app.exception_handler(HTTPException)
async def http_exception_handler(request: Request, exc: HTTPException):
    """Handle HTTP exceptions with structured response."""
    return JSONResponse(
        status_code=exc.status_code,
        content={
            "status": "error",
            "message": exc.detail,
            "timestamp": datetime.utcnow().isoformat(),
            "path": str(request.url),
        },
    )


@app.exception_handler(Exception)
async def general_exception_handler(request: Request, exc: Exception):
    """Handle general exceptions with logging."""
    logger.error(f"Unhandled exception: {exc}")
    return JSONResponse(
        status_code=500,
        content={
            "status": "error",
            "message": "Internal server error",
            "timestamp": datetime.utcnow().isoformat(),
        },
    )


def main():
    """Start Keryx API Gateway service."""
    logger.info(f"Starting Keryx API Gateway on {API_HOST}:{API_PORT}")

    uvicorn.run(app, host=API_HOST, port=API_PORT, log_level="info", access_log=True)


if __name__ == "__main__":
    main()
