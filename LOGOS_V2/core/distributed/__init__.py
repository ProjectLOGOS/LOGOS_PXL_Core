"""
LOGOS V2 Distributed Systems
Worker integration and distributed computing capabilities
"""

from .worker_integration import (
    WorkerIntegrationSystem,
    get_worker_integration,
    initialize_workers,
    WorkerType,
    WorkerConfig,
    WorkerRequest,
    WorkerResponse,
    WorkerIntegrationError
)

__all__ = [
    "WorkerIntegrationSystem",
    "get_worker_integration", 
    "initialize_workers",
    "WorkerType",
    "WorkerConfig",
    "WorkerRequest",
    "WorkerResponse",
    "WorkerIntegrationError"
]