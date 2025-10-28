"""
Worker Integration System for LOGOS V2

Provides unified interface to the distributed microservice workers:
- TETRAGNOS: Pattern recognition and machine learning
- TELOS: Causal reasoning and scientific inference
- THONOC: Symbolic reasoning and formal mathematics

This module enables seamless integration of worker capabilities into the main LOGOS system.
"""

import asyncio
import aiohttp
import json
import logging
from typing import Dict, List, Any, Optional, Union
from dataclasses import dataclass
from enum import Enum
import time

logger = logging.getLogger(__name__)

class WorkerType(Enum):
    """Types of reasoning workers"""
    TETRAGNOS = "tetragnos"
    TELOS = "telos"
    THONOC = "thonoc"

@dataclass
class WorkerConfig:
    """Configuration for a worker service"""
    name: str
    url: str
    timeout: int = 30
    retries: int = 3

@dataclass
class WorkerRequest:
    """Request to send to a worker"""
    worker_type: WorkerType
    task: str
    parameters: Dict[str, Any]
    priority: str = "normal"
    timeout: Optional[int] = None

@dataclass
class WorkerResponse:
    """Response from a worker"""
    success: bool
    result: Any
    worker_type: WorkerType
    execution_time: float
    error: Optional[str] = None

class WorkerIntegrationError(Exception):
    """Error raised when worker integration fails"""
    pass

class WorkerIntegrationSystem:
    """
    Unified interface for integrating reasoning workers into LOGOS V2

    Provides load balancing, health monitoring, and task routing across
    the distributed microservice architecture.
    """

    def __init__(self):
        self.workers = {
            WorkerType.TETRAGNOS: WorkerConfig(
                name="TETRAGNOS",
                url="http://localhost:8065",
                timeout=60
            ),
            WorkerType.TELOS: WorkerConfig(
                name="TELOS",
                url="http://localhost:8066",
                timeout=120
            ),
            WorkerType.THONOC: WorkerConfig(
                name="THONOC",
                url="http://localhost:8067",
                timeout=90
            )
        }

        self.session: Optional[aiohttp.ClientSession] = None
        self.health_cache = {}
        self.cache_timeout = 30  # seconds

    async def __aenter__(self):
        """Async context manager entry"""
        self.session = aiohttp.ClientSession()
        return self

    async def __aexit__(self, exc_type, exc_val, exc_tb):
        """Async context manager exit"""
        if self.session:
            await self.session.close()

    def _get_worker_config(self, worker_type: WorkerType) -> WorkerConfig:
        """Get configuration for a worker type"""
        return self.workers[worker_type]

    async def _check_worker_health(self, worker_type: WorkerType) -> bool:
        """Check if a worker service is healthy"""
        cache_key = worker_type.value
        current_time = time.time()

        # Check cache first
        if cache_key in self.health_cache:
            cached_time, is_healthy = self.health_cache[cache_key]
            if current_time - cached_time < self.cache_timeout:
                return is_healthy

        config = self._get_worker_config(worker_type)

        try:
            async with self.session.get(f"{config.url}/health", timeout=5) as response:
                is_healthy = response.status == 200
        except Exception:
            is_healthy = False

        # Cache result
        self.health_cache[cache_key] = (current_time, is_healthy)
        return is_healthy

    async def _call_worker(self, request: WorkerRequest) -> WorkerResponse:
        """Call a specific worker with retry logic"""
        config = self._get_worker_config(request.worker_type)
        timeout = request.timeout or config.timeout

        payload = {
            "task": request.task,
            "parameters": request.parameters,
            "priority": request.priority
        }

        start_time = time.time()

        for attempt in range(config.retries):
            try:
                async with self.session.post(
                    f"{config.url}/process",
                    json=payload,
                    timeout=timeout
                ) as response:

                    if response.status == 200:
                        result = await response.json()
                        execution_time = time.time() - start_time

                        return WorkerResponse(
                            success=True,
                            result=result,
                            worker_type=request.worker_type,
                            execution_time=execution_time
                        )
                    else:
                        error_text = await response.text()
                        logger.warning(f"Worker {config.name} returned status {response.status}: {error_text}")

            except asyncio.TimeoutError:
                logger.warning(f"Timeout calling {config.name} (attempt {attempt + 1})")
            except Exception as e:
                logger.error(f"Error calling {config.name}: {e}")

            # Wait before retry
            if attempt < config.retries - 1:
                await asyncio.sleep(1)

        execution_time = time.time() - start_time
        return WorkerResponse(
            success=False,
            result=None,
            worker_type=request.worker_type,
            execution_time=execution_time,
            error=f"Failed to call {config.name} after {config.retries} attempts"
        )

    async def execute_task(self, request: WorkerRequest) -> WorkerResponse:
        """Execute a task on the appropriate worker"""
        # Check worker health first
        if not await self._check_worker_health(request.worker_type):
            return WorkerResponse(
                success=False,
                result=None,
                worker_type=request.worker_type,
                execution_time=0.0,
                error=f"Worker {request.worker_type.value} is not healthy"
            )

        return await self._call_worker(request)

    async def pattern_recognition(self, data: Any, **kwargs) -> WorkerResponse:
        """Execute pattern recognition using TETRAGNOS"""
        request = WorkerRequest(
            worker_type=WorkerType.TETRAGNOS,
            task="pattern_recognition",
            parameters={"data": data, **kwargs}
        )
        return await self.execute_task(request)

    async def causal_reasoning(self, hypothesis: str, data: Any = None, **kwargs) -> WorkerResponse:
        """Execute causal reasoning using TELOS"""
        request = WorkerRequest(
            worker_type=WorkerType.TELOS,
            task="causal_analysis",
            parameters={"hypothesis": hypothesis, "data": data, **kwargs}
        )
        return await self.execute_task(request)

    async def symbolic_reasoning(self, formula: str, **kwargs) -> WorkerResponse:
        """Execute symbolic reasoning using THONOC"""
        request = WorkerRequest(
            worker_type=WorkerType.THONOC,
            task="symbolic_computation",
            parameters={"formula": formula, **kwargs}
        )
        return await self.execute_task(request)

    async def get_system_status(self) -> Dict[str, Any]:
        """Get status of all worker systems"""
        status = {}

        for worker_type in WorkerType:
            config = self._get_worker_config(worker_type)
            is_healthy = await self._check_worker_health(worker_type)

            status[worker_type.value] = {
                "name": config.name,
                "url": config.url,
                "healthy": is_healthy,
                "timeout": config.timeout,
                "retries": config.retries
            }

        return status

# Global instance
_worker_integration = None

def get_worker_integration() -> WorkerIntegrationSystem:
    """Get the global worker integration instance"""
    global _worker_integration
    if _worker_integration is None:
        _worker_integration = WorkerIntegrationSystem()
    return _worker_integration

async def initialize_workers() -> bool:
    """Initialize and verify all worker systems"""
    integration = get_worker_integration()

    async with integration:
        status = await integration.get_system_status()

        healthy_count = sum(1 for worker in status.values() if worker["healthy"])
        total_count = len(status)

        logger.info(f"Worker initialization: {healthy_count}/{total_count} systems healthy")

        for worker_name, worker_status in status.items():
            if worker_status["healthy"]:
                logger.info(f"✓ {worker_name} ({worker_status['url']}) is operational")
            else:
                logger.warning(f"✗ {worker_name} ({worker_status['url']}) is not responding")

        return healthy_count == total_count
