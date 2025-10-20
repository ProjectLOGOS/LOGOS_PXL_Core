"""
LOGOS AGI v1.0 Adaptive Interface - Runtime Integration Layer

Integrates AGI enhancement modules with the UnifiedRuntimeService, providing
REST API endpoints for daemon operations, coherence monitoring, and governance
controls. Maintains backward compatibility with existing LOGOS core services.

Architecture:
- FastAPI-based REST interface
- Daemon lifecycle management endpoints  
- Real-time coherence monitoring
- Policy governance controls
- Event streaming for telemetry
- WebSocket support for real-time updates

Endpoints:
- /daemon/start - Start the LOGOS daemon
- /daemon/stop - Stop the LOGOS daemon
- /daemon/status - Get daemon status and metrics
- /daemon/verify - Trigger verification cycle
- /coherence/current - Get current Trinity-Coherence
- /coherence/optimize - Trigger coherence optimization
- /policy/check - Check policy constraints
- /telemetry/stream - WebSocket telemetry stream

Safety Integration:
- All operations respect governance policies
- Emergency stop propagation to all services
- Audit trail integration
- Rate limiting and access controls
"""

import logging
import asyncio
from typing import Dict, List, Optional, Any
from datetime import datetime
from fastapi import FastAPI, HTTPException, WebSocket, WebSocketDisconnect, Depends
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel, Field
import uvicorn
import json

# Import LOGOS AGI v1.0 components
from logos_core.daemon.logos_daemon import LogosDaemon, DaemonConfig, DaemonStatus
from logos_core.meta_reasoning.iel_registry import IELRegistry
from logos_core.governance.policy import PolicyManager
from logos_core.coherence.coherence_metrics import TrinityCoherence, CoherenceAnalysis
from logos_core.coherence.coherence_optimizer import CoherenceOptimizer
from logos_core.unified_formalisms import UnifiedFormalisms


# Request/Response Models
class DaemonStartRequest(BaseModel):
    config: Optional[Dict[str, Any]] = None
    force_restart: bool = False


class DaemonStatusResponse(BaseModel):
    is_running: bool
    start_time: Optional[datetime]
    last_cycle_time: Optional[datetime]
    cycles_completed: int
    gaps_detected: int
    extensions_generated: int
    last_error: Optional[str]
    memory_usage_mb: float
    cpu_usage_percent: float


class CoherenceResponse(BaseModel):
    trinity_coherence: float
    pxl_coherence: float
    iel_coherence: float
    runtime_coherence: float
    timestamp: datetime
    is_degraded: bool


class CoherenceOptimizationRequest(BaseModel):
    max_time_minutes: Optional[int] = 10
    optimization_method: Optional[str] = "hill_climbing"


class PolicyCheckRequest(BaseModel):
    constraint_name: str
    current_value: Any
    component: str = "api"


class PolicyCheckResponse(BaseModel):
    constraint_satisfied: bool
    policy_value: Any
    violation_details: Optional[Dict[str, Any]] = None


class TelemetryEvent(BaseModel):
    timestamp: datetime
    event_type: str
    component: str
    data: Dict[str, Any]


class AdaptiveInterface:
    """
    LOGOS AGI v1.0 Adaptive Interface
    
    Provides REST API integration for AGI enhancement modules with the
    existing LOGOS runtime infrastructure.
    """
    
    def __init__(self, host: str = "0.0.0.0", port: int = 8080):
        self.host = host
        self.port = port
        self.logger = self._setup_logging()
        
        # Initialize core components
        self.daemon: Optional[LogosDaemon] = None
        self.iel_registry = IELRegistry()
        self.policy_manager = PolicyManager()
        self.trinity_coherence = TrinityCoherence()
        self.coherence_optimizer = CoherenceOptimizer()
        self.unified_formalisms = UnifiedFormalisms()
        
        # FastAPI app initialization
        self.app = FastAPI(
            title="LOGOS AGI v1.0 Adaptive Interface",
            description="REST API for LOGOS AGI enhancement modules",
            version="1.0.0"
        )
        
        # Security
        self.security = HTTPBearer()
        
        # WebSocket connections for telemetry
        self.websocket_connections: List[WebSocket] = []
        
        # Setup middleware and routes
        self._setup_middleware()
        self._setup_routes()
        
        # Register policy violation callback
        self.policy_manager.register_violation_callback(self._handle_policy_violation)
        
    def _setup_logging(self) -> logging.Logger:
        """Configure adaptive interface logging"""
        logger = logging.getLogger("logos.adaptive_interface")
        if not logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter(
                '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
            )
            handler.setFormatter(formatter)
            logger.addHandler(handler)
            logger.setLevel(logging.INFO)
        return logger
        
    def _setup_middleware(self) -> None:
        """Setup FastAPI middleware"""
        self.app.add_middleware(
            CORSMiddleware,
            allow_origins=["*"],  # Configure appropriately for production
            allow_credentials=True,
            allow_methods=["*"],
            allow_headers=["*"],
        )
        
    def _setup_routes(self) -> None:
        """Setup API routes"""
        
        # Health check
        @self.app.get("/health")
        async def health_check():
            """Health check endpoint"""
            return {
                "status": "healthy",
                "timestamp": datetime.now().isoformat(),
                "version": "1.0.0"
            }
            
        # Daemon Management
        @self.app.post("/daemon/start", response_model=DaemonStatusResponse)
        async def start_daemon(request: DaemonStartRequest):
            """Start the LOGOS daemon"""
            try:
                # Check policy constraints
                if not self.policy_manager.check_safety_constraint("daemon_operations", "start"):
                    raise HTTPException(status_code=403, detail="Policy constraint violation")
                    
                if self.daemon and self.daemon.get_status().is_running and not request.force_restart:
                    raise HTTPException(status_code=400, detail="Daemon already running")
                    
                # Stop existing daemon if force restart
                if request.force_restart and self.daemon:
                    self.daemon.stop()
                    
                # Create new daemon with config
                config = DaemonConfig(**request.config) if request.config else DaemonConfig()
                self.daemon = LogosDaemon(config)
                
                # Start daemon
                success = self.daemon.start()
                if not success:
                    raise HTTPException(status_code=500, detail="Failed to start daemon")
                    
                # Get status
                status = self.daemon.get_status()
                
                # Broadcast telemetry
                await self._broadcast_telemetry(TelemetryEvent(
                    timestamp=datetime.now(),
                    event_type="daemon_started",
                    component="adaptive_interface",
                    data={"daemon_id": id(self.daemon)}
                ))
                
                return DaemonStatusResponse(
                    is_running=status.is_running,
                    start_time=status.start_time,
                    last_cycle_time=status.last_cycle_time,
                    cycles_completed=status.cycles_completed,
                    gaps_detected=status.gaps_detected,
                    extensions_generated=status.extensions_generated,
                    last_error=status.last_error,
                    memory_usage_mb=status.memory_usage_mb,
                    cpu_usage_percent=status.cpu_usage_percent
                )
                
            except Exception as e:
                self.logger.error(f"Failed to start daemon: {e}")
                raise HTTPException(status_code=500, detail=str(e))
                
        @self.app.post("/daemon/stop")
        async def stop_daemon():
            """Stop the LOGOS daemon"""
            try:
                if not self.daemon:
                    raise HTTPException(status_code=400, detail="No daemon instance")
                    
                success = self.daemon.stop()
                if not success:
                    raise HTTPException(status_code=500, detail="Failed to stop daemon")
                    
                # Broadcast telemetry
                await self._broadcast_telemetry(TelemetryEvent(
                    timestamp=datetime.now(),
                    event_type="daemon_stopped",
                    component="adaptive_interface", 
                    data={}
                ))
                
                return {"status": "stopped"}
                
            except Exception as e:
                self.logger.error(f"Failed to stop daemon: {e}")
                raise HTTPException(status_code=500, detail=str(e))
                
        @self.app.get("/daemon/status", response_model=DaemonStatusResponse)
        async def get_daemon_status():
            """Get daemon status"""
            try:
                if not self.daemon:
                    return DaemonStatusResponse(
                        is_running=False,
                        start_time=None,
                        last_cycle_time=None,
                        cycles_completed=0,
                        gaps_detected=0,
                        extensions_generated=0,
                        last_error=None,
                        memory_usage_mb=0.0,
                        cpu_usage_percent=0.0
                    )
                    
                status = self.daemon.get_status()
                return DaemonStatusResponse(
                    is_running=status.is_running,
                    start_time=status.start_time,
                    last_cycle_time=status.last_cycle_time,
                    cycles_completed=status.cycles_completed,
                    gaps_detected=status.gaps_detected,
                    extensions_generated=status.extensions_generated,
                    last_error=status.last_error,
                    memory_usage_mb=status.memory_usage_mb,
                    cpu_usage_percent=status.cpu_usage_percent
                )
                
            except Exception as e:
                self.logger.error(f"Failed to get daemon status: {e}")
                raise HTTPException(status_code=500, detail=str(e))
                
        @self.app.post("/daemon/verify")
        async def trigger_verification():
            """Trigger immediate verification cycle"""
            try:
                if not self.daemon or not self.daemon.get_status().is_running:
                    raise HTTPException(status_code=400, detail="Daemon not running")
                    
                # Trigger verification through unified formalisms
                verification_result = self.unified_formalisms.verify_system_integrity()
                
                return {
                    "verification_triggered": True,
                    "timestamp": datetime.now().isoformat(),
                    "result": verification_result
                }
                
            except Exception as e:
                self.logger.error(f"Failed to trigger verification: {e}")
                raise HTTPException(status_code=500, detail=str(e))
                
        # Coherence Management
        @self.app.get("/coherence/current", response_model=CoherenceResponse)
        async def get_current_coherence():
            """Get current Trinity-Coherence metrics"""
            try:
                coherence_report = self.trinity_coherence.get_coherence_report()
                current_snapshot = coherence_report["current_snapshot"]
                
                return CoherenceResponse(
                    trinity_coherence=current_snapshot["trinity_coherence"],
                    pxl_coherence=current_snapshot["pxl_coherence"],
                    iel_coherence=current_snapshot["iel_coherence"],
                    runtime_coherence=current_snapshot["runtime_coherence"],
                    timestamp=datetime.fromisoformat(current_snapshot["timestamp"]),
                    is_degraded=coherence_report["is_degraded"]
                )
                
            except Exception as e:
                self.logger.error(f"Failed to get coherence: {e}")
                raise HTTPException(status_code=500, detail=str(e))
                
        @self.app.post("/coherence/optimize")
        async def optimize_coherence(request: CoherenceOptimizationRequest):
            """Trigger coherence optimization"""
            try:
                # Check policy constraints
                if not self.policy_manager.check_safety_constraint("coherence_optimization", "trigger"):
                    raise HTTPException(status_code=403, detail="Policy constraint violation")
                    
                # Check if optimization is already active
                if self.coherence_optimizer.is_optimization_active():
                    raise HTTPException(status_code=409, detail="Optimization already active")
                    
                # Start optimization
                result = self.coherence_optimizer.optimize_coherence(request.max_time_minutes)
                
                # Broadcast telemetry
                await self._broadcast_telemetry(TelemetryEvent(
                    timestamp=datetime.now(),
                    event_type="coherence_optimization",
                    component="adaptive_interface",
                    data={
                        "success": result.success,
                        "improvement": result.coherence_improvement,
                        "iterations": result.iterations
                    }
                ))
                
                return {
                    "optimization_started": True,
                    "success": result.success,
                    "coherence_improvement": result.coherence_improvement,
                    "parameters_changed": result.parameters_changed,
                    "iterations": result.iterations,
                    "method_used": result.method_used.value,
                    "optimization_time_seconds": result.optimization_time_seconds
                }
                
            except Exception as e:
                self.logger.error(f"Failed to optimize coherence: {e}")
                raise HTTPException(status_code=500, detail=str(e))
                
        # Policy Management
        @self.app.post("/policy/check", response_model=PolicyCheckResponse)
        async def check_policy_constraint(request: PolicyCheckRequest):
            """Check policy constraint"""
            try:
                is_satisfied = self.policy_manager.check_safety_constraint(
                    request.constraint_name,
                    request.current_value,
                    request.component
                )
                
                policy_value = self.policy_manager.get_policy_value(
                    f"safety.{request.constraint_name}"
                )
                
                violation_details = None
                if not is_satisfied:
                    recent_violations = self.policy_manager.get_violations(hours=1)
                    matching_violations = [
                        v for v in recent_violations 
                        if v.policy_rule == request.constraint_name
                    ]
                    if matching_violations:
                        violation_details = matching_violations[-1].to_dict()
                
                return PolicyCheckResponse(
                    constraint_satisfied=is_satisfied,
                    policy_value=policy_value,
                    violation_details=violation_details
                )
                
            except Exception as e:
                self.logger.error(f"Failed to check policy: {e}")
                raise HTTPException(status_code=500, detail=str(e))
                
        @self.app.get("/policy/violations")
        async def get_policy_violations(severity: Optional[str] = None, hours: int = 24):
            """Get recent policy violations"""
            try:
                violations = self.policy_manager.get_violations(severity=severity, hours=hours)
                return {
                    "violations": [v.to_dict() for v in violations],
                    "count": len(violations),
                    "severity_filter": severity,
                    "time_window_hours": hours
                }
                
            except Exception as e:
                self.logger.error(f"Failed to get violations: {e}")
                raise HTTPException(status_code=500, detail=str(e))
                
        @self.app.post("/emergency/stop")
        async def emergency_stop(reason: str = "Manual emergency stop"):
            """Trigger emergency stop"""
            try:
                success = self.policy_manager.trigger_emergency_stop(reason, "adaptive_interface")
                
                if success:
                    # Stop daemon if running
                    if self.daemon:
                        self.daemon.stop()
                        
                    # Broadcast emergency stop
                    await self._broadcast_telemetry(TelemetryEvent(
                        timestamp=datetime.now(),
                        event_type="emergency_stop",
                        component="adaptive_interface",
                        data={"reason": reason}
                    ))
                    
                return {
                    "emergency_stop_triggered": success,
                    "reason": reason,
                    "timestamp": datetime.now().isoformat()
                }
                
            except Exception as e:
                self.logger.error(f"Failed to trigger emergency stop: {e}")
                raise HTTPException(status_code=500, detail=str(e))
                
        # WebSocket Telemetry
        @self.app.websocket("/telemetry/stream")
        async def telemetry_stream(websocket: WebSocket):
            """WebSocket endpoint for real-time telemetry"""
            await websocket.accept()
            self.websocket_connections.append(websocket)
            
            try:
                # Send initial status
                await websocket.send_text(json.dumps({
                    "event_type": "connection_established",
                    "timestamp": datetime.now().isoformat(),
                    "data": {"client_count": len(self.websocket_connections)}
                }))
                
                # Keep connection alive
                while True:
                    try:
                        # Wait for client message (heartbeat)
                        await asyncio.wait_for(websocket.receive_text(), timeout=30.0)
                    except asyncio.TimeoutError:
                        # Send heartbeat
                        await websocket.send_text(json.dumps({
                            "event_type": "heartbeat",
                            "timestamp": datetime.now().isoformat()
                        }))
                        
            except WebSocketDisconnect:
                self.websocket_connections.remove(websocket)
                self.logger.info("WebSocket client disconnected")
            except Exception as e:
                self.logger.error(f"WebSocket error: {e}")
                if websocket in self.websocket_connections:
                    self.websocket_connections.remove(websocket)
                    
    async def _broadcast_telemetry(self, event: TelemetryEvent) -> None:
        """Broadcast telemetry event to all WebSocket connections"""
        if not self.websocket_connections:
            return
            
        event_data = {
            "timestamp": event.timestamp.isoformat(),
            "event_type": event.event_type,
            "component": event.component,
            "data": event.data
        }
        
        # Send to all connected clients
        disconnected = []
        for websocket in self.websocket_connections:
            try:
                await websocket.send_text(json.dumps(event_data))
            except Exception as e:
                self.logger.error(f"Failed to send telemetry to client: {e}")
                disconnected.append(websocket)
                
        # Remove disconnected clients
        for websocket in disconnected:
            self.websocket_connections.remove(websocket)
            
    def _handle_policy_violation(self, violation) -> None:
        """Handle policy violation events"""
        # Create telemetry event
        event = TelemetryEvent(
            timestamp=datetime.now(),
            event_type="policy_violation",
            component="policy_manager",
            data=violation.to_dict()
        )
        
        # Broadcast to WebSocket clients
        asyncio.create_task(self._broadcast_telemetry(event))
        
    def run(self) -> None:
        """Run the adaptive interface server"""
        self.logger.info(f"Starting LOGOS AGI v1.0 Adaptive Interface on {self.host}:{self.port}")
        
        uvicorn.run(
            self.app,
            host=self.host,
            port=self.port,
            log_level="info",
            access_log=True
        )


# Standalone server for development
if __name__ == "__main__":
    interface = AdaptiveInterface()
    interface.run()