# logos_agi_v2/services/archon_nexus/archon_nexus.py

"""Archon Nexus Main Service - Distributed Planning Coordination

Primary planning service managing goal decomposition, workflow design,
and distributed task execution across worker subsystems.

Key Responsibilities:
- Goal-to-workflow transformation
- Multi-subsystem task orchestration
- Execution state management
- Result synthesis and reporting

Dependencies: pika, json, networkx, core validation systems
"""

import json
import logging
import signal
import sys
import threading
import time
import uuid
from datetime import datetime
from typing import Any

import pika

# Core validation systems
try:
    from core.principles import PrincipleEngine
    from core.unified_formalisms import UnifiedFormalismValidator
    from shared.worker_config import RABBITMQ_CONFIG
except ImportError:

    class UnifiedFormalismValidator:
        def validate_agi_operation(self, request):
            return {"authorized": True, "token": f"avt_{uuid.uuid4().hex}"}

    class PrincipleEngine:
        def validate_principle_adherence(self, operation):
            return {"valid": True, "violations": []}

    RABBITMQ_CONFIG = {"host": "rabbitmq", "port": 5672, "heartbeat": 600}

# Service modules
from .agent_orchestrator import AgentOrchestrator
from .workflow_architect import WorkflowArchitect

# Configuration
SERVICE_NAME = "ARCHON_NEXUS"
RABBITMQ_HOST = RABBITMQ_CONFIG.get("host", "rabbitmq")
RABBITMQ_PORT = RABBITMQ_CONFIG.get("port", 5672)

# Queue configuration
ARCHON_GOALS_QUEUE = "archon_goals"
TASK_RESULT_QUEUE = "task_result_queue"
TETRAGNOS_QUEUE = "tetragnos_task_queue"
TELOS_QUEUE = "telos_task_queue"
THONOC_QUEUE = "thonoc_task_queue"
DB_WRITE_QUEUE = "db_write_queue"

# Logging setup
logging.basicConfig(
    level=logging.INFO,
    format=f"%(asctime)s - %(levelname)s - {SERVICE_NAME} - %(message)s",
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler("/app/logs/archon_nexus.log", mode="a"),
    ],
)


class ArchonNexus:
    """Primary planning service for distributed goal execution.

    Orchestrates workflow design and task execution through integrated
    architecture and orchestration modules for complex goal achievement.

    Core Operations:
    - Goal decomposition and workflow planning
    - Multi-subsystem task coordination
    - Execution progress monitoring
    - Result aggregation and synthesis
    """

    def __init__(self):
        self.logger = logging.getLogger("ARCHON_NEXUS")
        self.connection = None
        self.channel = None

        # Core validation systems
        self.validator = UnifiedFormalismValidator()
        self.principle_engine = PrincipleEngine()

        # Service modules
        self.workflow_architect = WorkflowArchitect(self.validator)
        self.agent_orchestrator = None  # Initialized after connection

        # Service state
        self.system_status = {
            "service_name": SERVICE_NAME,
            "status": "initializing",
            "started_at": datetime.utcnow().isoformat(),
            "workflows_processed": 0,
            "active_workflows": 0,
            "last_activity": datetime.utcnow().isoformat(),
        }

        self.shutdown_event = threading.Event()

        # Signal handlers
        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)

    def _signal_handler(self, signum, frame):
        """Handle system shutdown signals."""
        self.logger.info(f"Received signal {signum}, initiating shutdown...")
        self.shutdown_event.set()

    def _connect_rabbitmq(self) -> tuple[pika.BlockingConnection, pika.channel.Channel]:
        """Establish RabbitMQ connection with retry logic."""
        max_retries = 10
        retry_delay = 5

        for attempt in range(max_retries):
            try:
                connection = pika.BlockingConnection(
                    pika.ConnectionParameters(
                        host=RABBITMQ_HOST,
                        port=RABBITMQ_PORT,
                        heartbeat=RABBITMQ_CONFIG.get("heartbeat", 600),
                        blocked_connection_timeout=300,
                    )
                )
                channel = connection.channel()

                self.logger.info("RabbitMQ connection established")
                return connection, channel

            except Exception as e:
                self.logger.warning(f"Connection attempt {attempt + 1}/{max_retries} failed: {e}")
                if attempt < max_retries - 1:
                    time.sleep(retry_delay)
                else:
                    raise

    def _setup_queues(self):
        """Configure required message queues."""
        queues = [
            ARCHON_GOALS_QUEUE,
            TASK_RESULT_QUEUE,
            TETRAGNOS_QUEUE,
            TELOS_QUEUE,
            THONOC_QUEUE,
            DB_WRITE_QUEUE,
        ]

        for queue in queues:
            self.channel.queue_declare(queue=queue, durable=True)
            self.logger.info(f"Queue '{queue}' declared")

    def _setup_consumers(self):
        """Configure message consumers for goal and result processing."""
        # Goal request consumer
        self.channel.basic_qos(prefetch_count=1)
        self.channel.basic_consume(
            queue=ARCHON_GOALS_QUEUE, on_message_callback=self._handle_goal_message, auto_ack=False
        )

        # Task result consumer
        self.channel.basic_consume(
            queue=TASK_RESULT_QUEUE, on_message_callback=self._handle_result_message, auto_ack=False
        )

        self.logger.info("Message consumers configured")

    def _handle_goal_message(self, ch, method, properties, body):
        """Process incoming goal for workflow design and execution."""
        try:
            goal_data = json.loads(body.decode("utf-8"))
            goal_description = goal_data.get("query") or goal_data.get("goal")
            context = goal_data.get("context", {})

            self.logger.info(f"Processing goal: {goal_description}")

            # Design workflow for goal
            workflow = self.workflow_architect.design_workflow(goal_description, context)

            # Validate workflow structure
            if not self.workflow_architect.validate_workflow_structure(workflow):
                self.logger.error(f"Invalid workflow structure for goal: {goal_description}")
                ch.basic_nack(delivery_tag=method.delivery_tag, requeue=False)
                return

            # Execute workflow
            self.agent_orchestrator.execute_workflow(workflow)

            # Update system metrics
            self.system_status["workflows_processed"] += 1
            self.system_status["active_workflows"] += 1
            self.system_status["last_activity"] = datetime.utcnow().isoformat()

            ch.basic_ack(delivery_tag=method.delivery_tag)

        except Exception as e:
            self.logger.error(f"Goal processing error: {e}")
            ch.basic_nack(delivery_tag=method.delivery_tag, requeue=False)

    def _handle_result_message(self, ch, method, properties, body):
        """Process task result from worker subsystems."""
        try:
            result_data = json.loads(body.decode("utf-8"))

            # Forward to orchestrator for workflow state management
            self.agent_orchestrator.handle_task_result(result_data)

            # Update metrics on workflow completion
            if result_data.get("workflow_completed"):
                self.system_status["active_workflows"] -= 1

            self.system_status["last_activity"] = datetime.utcnow().isoformat()

            ch.basic_ack(delivery_tag=method.delivery_tag)

        except Exception as e:
            self.logger.error(f"Result processing error: {e}")
            ch.basic_nack(delivery_tag=method.delivery_tag, requeue=False)

    def get_system_status(self) -> dict[str, Any]:
        """Generate comprehensive system status report."""
        orchestrator_status = (
            self.agent_orchestrator.get_orchestrator_status() if self.agent_orchestrator else {}
        )

        status = dict(self.system_status)
        status.update(
            {
                "orchestrator_metrics": orchestrator_status,
                "validator_status": "operational",
                "workflow_architect_status": "operational",
                "timestamp": datetime.utcnow().isoformat(),
            }
        )

        return status

    def start(self):
        """Initialize and start Archon Nexus service."""
        self.logger.info("Starting Archon Nexus service...")

        try:
            # Initialize connections
            self.connection, self.channel = self._connect_rabbitmq()

            # Initialize orchestrator with connection
            self.agent_orchestrator = AgentOrchestrator(self.connection, self.channel)

            # Configure infrastructure
            self._setup_queues()
            self._setup_consumers()

            self.system_status["status"] = "running"
            self.logger.info("Archon Nexus service operational")

            # Message processing loop
            self.logger.info("Awaiting goals...")

            while not self.shutdown_event.is_set():
                try:
                    self.connection.process_data_events(time_limit=1)
                except KeyboardInterrupt:
                    break
                except Exception as e:
                    self.logger.error(f"Main loop error: {e}")
                    time.sleep(1)

        except Exception as e:
            self.logger.error(f"Service startup error: {e}")
            self.system_status["status"] = "error"
            raise
        finally:
            self.stop()

    def stop(self):
        """Terminate Archon Nexus service with cleanup."""
        self.logger.info("Stopping Archon Nexus service...")

        self.system_status["status"] = "stopping"

        # Close connections
        if self.connection and not self.connection.is_closed:
            self.connection.close()

        self.system_status["status"] = "stopped"
        self.logger.info("Archon Nexus service terminated")


def main():
    """Service entry point."""
    service = ArchonNexus()

    try:
        service.start()
    except KeyboardInterrupt:
        service.logger.info("Service interrupted")
    except Exception as e:
        service.logger.error(f"Service failed: {e}")
        sys.exit(1)


if __name__ == "__main__":
    main()
