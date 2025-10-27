#!/usr/bin/env python3
"""
Agent Communication Framework - Multi-Agent LOGOS System

This module enables LOGOS instances to discover, communicate, and coordinate
with other agents in a distributed reasoning network. Provides secure
JSON-RPC API for IEL exchange, capability sharing, and trust management.

Features:
- Agent discovery and registration
- Secure communication channels
- Trust metric tracking and management
- Capability advertisement and matching
- Health monitoring and failure detection

Part of the LOGOS AGI v1.0 multi-agent reasoning framework.
"""

import json
import logging
import socket
import threading
import time
import uuid
from dataclasses import dataclass, asdict
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Optional, Set, Any, Callable
from socketserver import ThreadingTCPServer, BaseRequestHandler
from urllib.parse import urlparse
import hashlib
import hmac

# Cryptographic imports
try:
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import rsa, padding
    from cryptography.hazmat.primitives.serialization import load_pem_public_key, load_pem_private_key
    CRYPTO_AVAILABLE = True
except ImportError:
    CRYPTO_AVAILABLE = False
    logging.warning("Cryptography not available, using basic security")

logger = logging.getLogger(__name__)

@dataclass
class AgentCapabilities:
    """Agent capability description"""
    domains: List[str]              # Logic domains (modal, temporal, etc.)
    evaluators: List[str]           # Available evaluators
    generators: List[str]           # Available IEL generators
    max_concurrent_requests: int    # Request handling capacity
    specializations: List[str]      # Special capabilities
    version: str                    # Agent version

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'AgentCapabilities':
        return cls(**data)

@dataclass
class TrustMetrics:
    """Trust and reputation metrics for an agent"""
    trust_score: float              # Overall trust (0.0 - 1.0)
    successful_exchanges: int       # Successful IEL exchanges
    failed_exchanges: int           # Failed exchanges
    invalid_iels_sent: int          # Invalid IELs received from agent
    response_time_avg: float        # Average response time (seconds)
    last_successful_contact: datetime
    reputation_decay_rate: float = 0.99  # Daily decay for inactive agents

    def calculate_reliability(self) -> float:
        """Calculate reliability based on exchange history"""
        total = self.successful_exchanges + self.failed_exchanges
        if total == 0:
            return 1.0  # Benefit of doubt for new agents
        return self.successful_exchanges / total

    def update_success(self, response_time: float):
        """Update metrics after successful exchange"""
        self.successful_exchanges += 1
        self.last_successful_contact = datetime.now()

        # Update average response time
        if self.response_time_avg == 0:
            self.response_time_avg = response_time
        else:
            self.response_time_avg = (self.response_time_avg + response_time) / 2

        # Improve trust score
        reliability = self.calculate_reliability()
        self.trust_score = min(1.0, self.trust_score * 0.95 + reliability * 0.05)

    def update_failure(self, reason: str = "unknown"):
        """Update metrics after failed exchange"""
        self.failed_exchanges += 1

        if "invalid" in reason.lower() or "malformed" in reason.lower():
            self.invalid_iels_sent += 1

        # Reduce trust score
        reliability = self.calculate_reliability()
        self.trust_score = max(0.0, self.trust_score * 0.9 - (1 - reliability) * 0.1)

    def decay_reputation(self):
        """Apply daily reputation decay for inactive agents"""
        days_since_contact = (datetime.now() - self.last_successful_contact).days
        if days_since_contact > 0:
            self.trust_score *= (self.reputation_decay_rate ** days_since_contact)

    def to_dict(self) -> Dict[str, Any]:
        data = asdict(self)
        data['last_successful_contact'] = self.last_successful_contact.isoformat()
        return data

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'TrustMetrics':
        if isinstance(data['last_successful_contact'], str):
            data['last_successful_contact'] = datetime.fromisoformat(data['last_successful_contact'])
        return cls(**data)

@dataclass
class AgentNode:
    """Represents a LOGOS agent in the multi-agent network"""
    agent_id: str                   # Unique agent identifier
    host: str                       # Network address
    port: int                       # Communication port
    public_key: Optional[str] = None # RSA public key for verification
    capabilities: Optional[AgentCapabilities] = None
    trust_metrics: Optional[TrustMetrics] = None
    status: str = "unknown"         # online, offline, degraded
    last_seen: Optional[datetime] = None
    metadata: Dict[str, Any] = None

    def __post_init__(self):
        if self.trust_metrics is None:
            self.trust_metrics = TrustMetrics(
                trust_score=0.5,  # Neutral starting trust
                successful_exchanges=0,
                failed_exchanges=0,
                invalid_iels_sent=0,
                response_time_avg=0.0,
                last_successful_contact=datetime.now()
            )
        if self.metadata is None:
            self.metadata = {}

    @property
    def address(self) -> str:
        """Get agent network address"""
        return f"{self.host}:{self.port}"

    @property
    def is_trusted(self) -> bool:
        """Check if agent meets minimum trust threshold"""
        return self.trust_metrics.trust_score >= 0.3

    @property
    def is_responsive(self) -> bool:
        """Check if agent has responded recently"""
        if not self.last_seen:
            return False
        return (datetime.now() - self.last_seen) < timedelta(hours=1)

    def update_status(self, status: str):
        """Update agent status and timestamp"""
        self.status = status
        self.last_seen = datetime.now()

    def to_dict(self) -> Dict[str, Any]:
        data = asdict(self)
        if self.last_seen:
            data['last_seen'] = self.last_seen.isoformat()
        if self.capabilities:
            data['capabilities'] = self.capabilities.to_dict()
        if self.trust_metrics:
            data['trust_metrics'] = self.trust_metrics.to_dict()
        return data

    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'AgentNode':
        if data.get('last_seen') and isinstance(data['last_seen'], str):
            data['last_seen'] = datetime.fromisoformat(data['last_seen'])
        if data.get('capabilities'):
            data['capabilities'] = AgentCapabilities.from_dict(data['capabilities'])
        if data.get('trust_metrics'):
            data['trust_metrics'] = TrustMetrics.from_dict(data['trust_metrics'])
        return cls(**data)

class JSONRPCHandler(BaseRequestHandler):
    """Handle JSON-RPC requests for agent communication"""

    def __init__(self, request, client_address, server):
        self.comm_manager = server.comm_manager
        super().__init__(request, client_address, server)

    def handle(self):
        """Handle incoming JSON-RPC request"""
        try:
            # Read request data
            data = self.request.recv(4096).decode('utf-8')
            if not data:
                return

            request = json.loads(data)
            response = self.process_request(request)

            # Send response
            response_data = json.dumps(response).encode('utf-8')
            self.request.sendall(response_data)

        except Exception as e:
            logger.error(f"Error handling request: {e}")
            error_response = {
                "jsonrpc": "2.0",
                "error": {"code": -32603, "message": "Internal error"},
                "id": None
            }
            self.request.sendall(json.dumps(error_response).encode('utf-8'))

    def process_request(self, request: Dict) -> Dict:
        """Process JSON-RPC request and return response"""
        try:
            method = request.get('method')
            params = request.get('params', {})
            request_id = request.get('id')

            if method == 'ping':
                result = self.comm_manager.handle_ping(params)
            elif method == 'get_capabilities':
                result = self.comm_manager.handle_get_capabilities(params)
            elif method == 'register_agent':
                result = self.comm_manager.handle_register_agent(params)
            elif method == 'sync_iels':
                result = self.comm_manager.handle_sync_iels(params)
            elif method == 'get_agent_status':
                result = self.comm_manager.handle_get_agent_status(params)
            else:
                return {
                    "jsonrpc": "2.0",
                    "error": {"code": -32601, "message": f"Method not found: {method}"},
                    "id": request_id
                }

            return {
                "jsonrpc": "2.0",
                "result": result,
                "id": request_id
            }

        except Exception as e:
            logger.error(f"Error processing request: {e}")
            return {
                "jsonrpc": "2.0",
                "error": {"code": -32000, "message": str(e)},
                "id": request.get('id')
            }

class AgentCommunicationManager:
    """Manages communication between LOGOS agents"""

    def __init__(self, agent_id: str = None, host: str = "localhost", port: int = 8750):
        self.agent_id = agent_id or str(uuid.uuid4())
        self.host = host
        self.port = port
        self.agents: Dict[str, AgentNode] = {}
        self.server = None
        self.running = False

        # Agent capabilities
        self.capabilities = AgentCapabilities(
            domains=["modal_logic", "temporal_logic", "iel"],
            evaluators=["ModalLogicEvaluator", "IELEvaluator"],
            generators=["IELGenerator"],
            max_concurrent_requests=10,
            specializations=["autonomous_learning", "coherence_optimization"],
            version="1.0.0"
        )

        # Security settings
        self.private_key = None
        self.public_key = None
        self._init_security()

        # Configuration
        self.config = {
            "discovery_interval": 30,      # Agent discovery interval (seconds)
            "health_check_interval": 60,   # Health check interval (seconds)
            "trust_update_interval": 300,  # Trust metrics update interval
            "max_retry_attempts": 3,       # Max retries for failed requests
            "request_timeout": 10,         # Request timeout (seconds)
            "min_trust_threshold": 0.3     # Minimum trust for IEL exchange
        }

        # Event handlers
        self.event_handlers: Dict[str, List[Callable]] = {
            "agent_discovered": [],
            "agent_lost": [],
            "iel_received": [],
            "trust_updated": []
        }

    def _init_security(self):
        """Initialize cryptographic keys"""
        if not CRYPTO_AVAILABLE:
            logger.warning("Cryptography unavailable, using mock security")
            return

        try:
            # Generate RSA key pair
            self.private_key = rsa.generate_private_key(
                public_exponent=65537,
                key_size=2048,
            )
            self.public_key = self.private_key.public_key()

            logger.info("Generated RSA key pair for agent security")

        except Exception as e:
            logger.error(f"Failed to initialize security: {e}")

    def get_public_key_pem(self) -> str:
        """Get public key in PEM format"""
        if not self.public_key or not CRYPTO_AVAILABLE:
            return ""

        try:
            pem = self.public_key.public_bytes(
                encoding=serialization.Encoding.PEM,
                format=serialization.PublicFormat.SubjectPublicKeyInfo
            )
            return pem.decode('utf-8')
        except Exception as e:
            logger.error(f"Failed to serialize public key: {e}")
            return ""

    def start_server(self) -> bool:
        """Start the agent communication server"""
        try:
            # Create threaded TCP server
            class CommunicationServer(ThreadingTCPServer):
                def __init__(self, server_address, RequestHandlerClass, comm_manager):
                    self.comm_manager = comm_manager
                    super().__init__(server_address, RequestHandlerClass)

            self.server = CommunicationServer(
                (self.host, self.port),
                JSONRPCHandler,
                self
            )

            # Start server in background thread
            server_thread = threading.Thread(target=self.server.serve_forever)
            server_thread.daemon = True
            server_thread.start()

            self.running = True
            logger.info(f"Agent communication server started on {self.host}:{self.port}")

            # Start background tasks
            self._start_background_tasks()

            return True

        except Exception as e:
            logger.error(f"Failed to start communication server: {e}")
            return False

    def stop_server(self):
        """Stop the agent communication server"""
        if self.server:
            self.server.shutdown()
            self.server.server_close()
            self.running = False
            logger.info("Agent communication server stopped")

    def _start_background_tasks(self):
        """Start background maintenance tasks"""
        # Agent discovery task
        discovery_thread = threading.Thread(target=self._discovery_loop)
        discovery_thread.daemon = True
        discovery_thread.start()

        # Health monitoring task
        health_thread = threading.Thread(target=self._health_check_loop)
        health_thread.daemon = True
        health_thread.start()

        # Trust metrics update task
        trust_thread = threading.Thread(target=self._trust_update_loop)
        trust_thread.daemon = True
        trust_thread.start()

    def _discovery_loop(self):
        """Background agent discovery loop"""
        while self.running:
            try:
                self.discover_agents()
                time.sleep(self.config["discovery_interval"])
            except Exception as e:
                logger.error(f"Error in discovery loop: {e}")

    def _health_check_loop(self):
        """Background health monitoring loop"""
        while self.running:
            try:
                self.check_agent_health()
                time.sleep(self.config["health_check_interval"])
            except Exception as e:
                logger.error(f"Error in health check loop: {e}")

    def _trust_update_loop(self):
        """Background trust metrics update loop"""
        while self.running:
            try:
                self.update_trust_metrics()
                time.sleep(self.config["trust_update_interval"])
            except Exception as e:
                logger.error(f"Error in trust update loop: {e}")

    def discover_agents(self, static_config_file: str = "agents.json"):
        """Discover other LOGOS agents"""
        # Static configuration discovery
        config_path = Path(static_config_file)
        if config_path.exists():
            try:
                with open(config_path, 'r') as f:
                    agent_configs = json.load(f)

                for config in agent_configs.get('agents', []):
                    if config['agent_id'] != self.agent_id:
                        agent = AgentNode.from_dict(config)
                        if agent.agent_id not in self.agents:
                            self.register_agent(agent)
                            self._emit_event("agent_discovered", agent)

            except Exception as e:
                logger.error(f"Error loading agent configuration: {e}")

        # TODO: Add network discovery (mDNS, broadcast, etc.)

    def register_agent(self, agent: AgentNode):
        """Register a discovered agent"""
        self.agents[agent.agent_id] = agent
        logger.info(f"Registered agent {agent.agent_id} at {agent.address}")

    def check_agent_health(self):
        """Check health of all registered agents"""
        for agent_id, agent in list(self.agents.items()):
            try:
                # Send ping request
                response = self._send_request(agent, "ping", {"timestamp": time.time()})

                if response and response.get('status') == 'ok':
                    agent.update_status("online")
                    agent.trust_metrics.update_success(response.get('response_time', 1.0))
                else:
                    agent.update_status("degraded")
                    agent.trust_metrics.update_failure("ping_failed")

            except Exception as e:
                logger.warning(f"Health check failed for agent {agent_id}: {e}")
                agent.update_status("offline")
                agent.trust_metrics.update_failure("health_check_failed")

                # Remove unresponsive agents after extended period
                if agent.last_seen and (datetime.now() - agent.last_seen) > timedelta(hours=24):
                    del self.agents[agent_id]
                    self._emit_event("agent_lost", agent)
                    logger.info(f"Removed unresponsive agent {agent_id}")

    def update_trust_metrics(self):
        """Update trust metrics for all agents"""
        for agent in self.agents.values():
            agent.trust_metrics.decay_reputation()
            self._emit_event("trust_updated", agent)

    def _send_request(self, agent: AgentNode, method: str, params: Dict, timeout: int = None) -> Optional[Dict]:
        """Send JSON-RPC request to agent"""
        timeout = timeout or self.config["request_timeout"]

        try:
            # Create socket connection
            sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            sock.settimeout(timeout)
            sock.connect((agent.host, agent.port))

            # Prepare request
            request = {
                "jsonrpc": "2.0",
                "method": method,
                "params": params,
                "id": str(uuid.uuid4())
            }

            # Send request
            request_data = json.dumps(request).encode('utf-8')
            sock.sendall(request_data)

            # Receive response
            response_data = sock.recv(4096).decode('utf-8')
            response = json.loads(response_data)

            sock.close()

            if "error" in response:
                logger.error(f"Agent {agent.agent_id} returned error: {response['error']}")
                return None

            return response.get("result")

        except Exception as e:
            logger.error(f"Failed to send request to {agent.agent_id}: {e}")
            return None

    def broadcast_message(self, method: str, params: Dict, trusted_only: bool = True) -> Dict[str, Any]:
        """Broadcast message to all agents"""
        results = {}

        for agent_id, agent in self.agents.items():
            if trusted_only and not agent.is_trusted:
                continue

            try:
                result = self._send_request(agent, method, params)
                results[agent_id] = result
            except Exception as e:
                logger.error(f"Broadcast failed to {agent_id}: {e}")
                results[agent_id] = {"error": str(e)}

        return results

    def _emit_event(self, event_type: str, data: Any):
        """Emit event to registered handlers"""
        for handler in self.event_handlers.get(event_type, []):
            try:
                handler(data)
            except Exception as e:
                logger.error(f"Error in event handler for {event_type}: {e}")

    def add_event_handler(self, event_type: str, handler: Callable):
        """Add event handler"""
        if event_type not in self.event_handlers:
            self.event_handlers[event_type] = []
        self.event_handlers[event_type].append(handler)

    # JSON-RPC method handlers
    def handle_ping(self, params: Dict) -> Dict:
        """Handle ping request"""
        request_time = params.get('timestamp', time.time())
        response_time = time.time() - request_time

        return {
            "status": "ok",
            "agent_id": self.agent_id,
            "response_time": response_time,
            "timestamp": time.time()
        }

    def handle_get_capabilities(self, params: Dict) -> Dict:
        """Handle capability request"""
        return {
            "agent_id": self.agent_id,
            "capabilities": self.capabilities.to_dict(),
            "status": "online",
            "public_key": self.get_public_key_pem()
        }

    def handle_register_agent(self, params: Dict) -> Dict:
        """Handle agent registration request"""
        try:
            agent_data = params.get('agent_info')
            agent = AgentNode.from_dict(agent_data)
            self.register_agent(agent)
            self._emit_event("agent_discovered", agent)

            return {
                "status": "registered",
                "agent_id": agent.agent_id
            }
        except Exception as e:
            logger.error(f"Agent registration failed: {e}")
            return {
                "status": "error",
                "message": str(e)
            }

    def handle_sync_iels(self, params: Dict) -> Dict:
        """Handle IEL synchronization request"""
        # This will be implemented in iel_sync_protocol.py
        return {
            "status": "not_implemented",
            "message": "IEL sync will be implemented in iel_sync_protocol.py"
        }

    def handle_get_agent_status(self, params: Dict) -> Dict:
        """Handle agent status request"""
        return {
            "agent_id": self.agent_id,
            "status": "online",
            "agents_known": len(self.agents),
            "trusted_agents": len([a for a in self.agents.values() if a.is_trusted]),
            "capabilities": self.capabilities.to_dict()
        }

    def get_trusted_agents(self) -> List[AgentNode]:
        """Get list of trusted agents"""
        return [agent for agent in self.agents.values() if agent.is_trusted]

    def get_agent_by_capability(self, capability: str) -> List[AgentNode]:
        """Get agents with specific capability"""
        matching_agents = []
        for agent in self.agents.values():
            if agent.capabilities and capability in agent.capabilities.specializations:
                matching_agents.append(agent)
        return matching_agents

    def get_network_status(self) -> Dict[str, Any]:
        """Get overall network status"""
        total_agents = len(self.agents)
        online_agents = len([a for a in self.agents.values() if a.status == "online"])
        trusted_agents = len([a for a in self.agents.values() if a.is_trusted])

        return {
            "agent_id": self.agent_id,
            "server_running": self.running,
            "total_agents": total_agents,
            "online_agents": online_agents,
            "trusted_agents": trusted_agents,
            "trust_ratio": trusted_agents / max(1, total_agents),
            "capabilities": self.capabilities.to_dict()
        }

# Global communication manager instance
_global_comm_manager = None

def get_global_comm_manager() -> AgentCommunicationManager:
    """Get global communication manager instance"""
    global _global_comm_manager
    if _global_comm_manager is None:
        _global_comm_manager = AgentCommunicationManager()
    return _global_comm_manager

def set_global_comm_manager(manager: AgentCommunicationManager):
    """Set global communication manager instance"""
    global _global_comm_manager
    _global_comm_manager = manager

if __name__ == "__main__":
    # Demo usage
    import argparse

    parser = argparse.ArgumentParser(description="LOGOS Agent Communication Demo")
    parser.add_argument("--agent-id", default=None, help="Agent ID")
    parser.add_argument("--host", default="localhost", help="Host address")
    parser.add_argument("--port", type=int, default=8750, help="Port number")
    parser.add_argument("--config", default="agents.json", help="Agent configuration file")

    args = parser.parse_args()

    # Setup logging
    logging.basicConfig(level=logging.INFO)

    # Create and start communication manager
    comm_manager = AgentCommunicationManager(
        agent_id=args.agent_id,
        host=args.host,
        port=args.port
    )

    if comm_manager.start_server():
        print(f"Agent {comm_manager.agent_id} started on {args.host}:{args.port}")
        print("Press Ctrl+C to stop...")

        try:
            while True:
                status = comm_manager.get_network_status()
                print(f"\nNetwork Status: {status['online_agents']}/{status['total_agents']} agents online")
                time.sleep(10)
        except KeyboardInterrupt:
            print("\nStopping agent...")
            comm_manager.stop_server()
    else:
        print("Failed to start communication server")
