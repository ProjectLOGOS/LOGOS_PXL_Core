# logos_agi_v2/services/archon_nexus/archon_nexus.py

"""
Archon Nexus - The Planner/Mind

The central planning and coordination service that designs and executes
complex multi-step workflows to achieve high-level goals.

Responsibilities:
- Goal decomposition and workflow design
- Task orchestration across worker subsystems
- Workflow state management and progress tracking
- Result aggregation and synthesis
- Error handling and recovery strategies
"""

import os
import sys
import json
import time
import logging
import signal
import uuid
import asyncio
from typing import Dict, List, Any, Optional, Set, Tuple
from datetime import datetime, timedelta
from dataclasses import dataclass, field
from enum import Enum
import threading
from concurrent.futures import ThreadPoolExecutor

# RabbitMQ and messaging
import pika
import pika.exceptions

# Graph processing for workflow DAGs
import networkx as nx

# Core LOGOS imports
try:
    from core.unified_formalisms import UnifiedFormalismValidator
    from core.principles import PrincipleEngine, validate_with_principles
    from core.data_structures import TaskDescriptor, OperationResult
    from shared.worker_config import WorkerType, TASK_TYPE_MAPPINGS, RABBITMQ_CONFIG
except ImportError:
    # Fallback implementations if core modules aren't available
    class UnifiedFormalismValidator:
        def validate_agi_operation(self, request): 
            return {"status": "authorized", "authorized": True, "token": f"avt_{uuid.uuid4().hex}"}
    
    def validate_with_principles(func):
        return func
    
    def generate_task_id(): 
        return f"task_{uuid.uuid4().hex[:8]}"
    
    class WorkerType(Enum):
        TETRAGNOS = "tetragnos"
        TELOS = "telos" 
        THONOC = "thonoc"
    
    TASK_TYPE_MAPPINGS = {
        WorkerType.TETRAGNOS: ['cluster_texts', 'translate_text', 'extract_features', 'analyze_patterns', 'semantic_similarity'],
        WorkerType.TELOS: ['predict_outcomes', 'causal_retrodiction', 'analyze_intervention', 'forecast_series', 'test_hypothesis', 'build_causal_model'],
        WorkerType.THONOC: ['construct_proof', 'assign_consequence', 'evaluate_lambda', 'modal_reasoning', 'consistency_check', 'theorem_proving']
    }
    
    RABBITMQ_CONFIG = {'host': 'rabbitmq', 'port': 5672, 'heartbeat': 600}

# Configuration
SERVICE_NAME = "ARCHON_NEXUS"
RABBITMQ_HOST = RABBITMQ_CONFIG.get('host', 'rabbitmq')
RABBITMQ_PORT = RABBITMQ_CONFIG.get('port', 5672)

# Queue configuration
ARCHON_GOALS_QUEUE = 'archon_goals'
TASK_RESULT_QUEUE = 'task_result_queue'
TETRAGNOS_QUEUE = 'tetragnos_task_queue'
TELOS_QUEUE = 'telos_task_queue'
THONOC_QUEUE = 'thonoc_task_queue'
DB_WRITE_QUEUE = 'db_write_queue'

# Logging setup
logging.basicConfig(
    level=logging.INFO,
    format=f'%(asctime)s - %(levelname)s - {SERVICE_NAME} - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler('/app/logs/archon_nexus.log', mode='a')
    ]
)

class WorkflowStatus(Enum):
    """Workflow execution status."""
    PENDING = "pending"
    PLANNING = "planning"
    EXECUTING = "executing"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"

class TaskStatus(Enum):
    """Individual task status."""
    PENDING = "pending"
    READY = "ready"
    EXECUTING = "executing"
    COMPLETED = "completed"
    FAILED = "failed"
    SKIPPED = "skipped"

@dataclass
class TaskNode:
    """Represents a single task in a workflow DAG."""
    task_id: str
    task_type: str
    subsystem: str
    payload: Dict[str, Any]
    dependencies: Set[str] = field(default_factory=set)
    status: TaskStatus = TaskStatus.PENDING
    result: Optional[Dict[str, Any]] = None
    error: Optional[str] = None
    start_time: Optional[datetime] = None
    end_time: Optional[datetime] = None
    retry_count: int = 0
    max_retries: int = 3

@dataclass
class WorkflowExecution:
    """Represents a complete workflow execution."""
    workflow_id: str
    goal_description: str
    status: WorkflowStatus = WorkflowStatus.PENDING
    tasks: Dict[str, TaskNode] = field(default_factory=dict)
    dag: nx.DiGraph = field(default_factory=nx.DiGraph)
    created_at: datetime = field(default_factory=datetime.utcnow)
    started_at: Optional[datetime] = None
    completed_at: Optional[datetime] = None
    result: Optional[Dict[str, Any]] = None
    error: Optional[str] = None

class WorkflowArchitect:
    """Designs workflow DAGs for complex goals."""
    
    def __init__(self, validator: UnifiedFormalismValidator):
        self.logger = logging.getLogger("WORKFLOW_ARCHITECT")
        self.validator = validator
        
    @validate_with_principles
    def design_workflow(self, goal_description: str, context: Dict[str, Any] = None) -> WorkflowExecution:
        """Design a DAG workflow for achieving the given goal."""
        
        workflow_id = f"wf_{uuid.uuid4().hex[:8]}"
        self.logger.info(f"Designing workflow {workflow_id} for goal: {goal_description}")
        
        # Validate the goal with the formal validator
        validation_request = {
            "entity": "workflow_goal",
            "proposition": goal_description,
            "operation": "design_workflow",
            "context": context or {}
        }
        
        validation_result = self.validator.validate_agi_operation(validation_request)
        
        if not validation_result.get("authorized", False):
            raise ValueError(f"Goal validation failed: {validation_result.get('reason', 'Unknown')}")
        
        # Create workflow execution
        workflow = WorkflowExecution(
            workflow_id=workflow_id,
            goal_description=goal_description,
            status=WorkflowStatus.PLANNING
        )
        
        # Decompose goal into tasks based on type analysis
        tasks = self._decompose_goal(goal_description, context)
        
        # Build DAG structure
        for task in tasks:
            workflow.tasks[task.task_id] = task
            workflow.dag.add_node(task.task_id, task=task)
        
        # Add dependencies
        self._add_task_dependencies(workflow)
        
        workflow.status = WorkflowStatus.PENDING
        self.logger.info(f"Workflow {workflow_id} designed with {len(tasks)} tasks")
        
        return workflow
    
    def _decompose_goal(self, goal_description: str, context: Dict[str, Any]) -> List[TaskNode]:
        """Decompose a high-level goal into executable tasks."""
        
        tasks = []
        goal_lower = goal_description.lower()
        
        # Analysis phase - understanding the goal
        if any(keyword in goal_lower for keyword in ['analyze', 'understand', 'examine', 'study']):
            # Start with text analysis
            analysis_task = TaskNode(
                task_id=f"task_{uuid.uuid4().hex[:8]}",
                task_type="extract_features",
                subsystem="tetragnos",
                payload={
                    "text": goal_description,
                    "analysis_type": "comprehensive",
                    "context": context
                }
            )
            tasks.append(analysis_task)
        
        # Prediction/modeling phase
        if any(keyword in goal_lower for keyword in ['predict', 'forecast', 'model', 'simulate']):
            prediction_task = TaskNode(
                task_id=f"task_{uuid.uuid4().hex[:8]}",
                task_type="predict_outcomes",
                subsystem="telos",
                payload={
                    "query": goal_description,
                    "prediction_type": "causal",
                    "context": context
                }
            )
            tasks.append(prediction_task)
        
        # Reasoning/proof phase
        if any(keyword in goal_lower for keyword in ['prove', 'verify', 'reason', 'logic']):
            reasoning_task = TaskNode(
                task_id=f"task_{uuid.uuid4().hex[:8]}",
                task_type="modal_reasoning",
                subsystem="thonoc",
                payload={
                    "proposition": goal_description,
                    "reasoning_type": "modal",
                    "context": context
                }
            )
            tasks.append(reasoning_task)
        
        # If no specific tasks identified, create a general analysis pipeline
        if not tasks:
            # Default pipeline: analysis -> prediction -> reasoning
            tasks = [
                TaskNode(
                    task_id=f"task_{uuid.uuid4().hex[:8]}",
                    task_type="analyze_patterns",
                    subsystem="tetragnos",
                    payload={"query": goal_description, "context": context}
                ),
                TaskNode(
                    task_id=f"task_{uuid.uuid4().hex[:8]}",
                    task_type="test_hypothesis",
                    subsystem="telos",
                    payload={"hypothesis": goal_description, "context": context}
                ),
                TaskNode(
                    task_id=f"task_{uuid.uuid4().hex[:8]}",
                    task_type="consistency_check",
                    subsystem="thonoc",
                    payload={"statement": goal_description, "context": context}
                )
            ]
        
        return tasks
    
    def _add_task_dependencies(self, workflow: WorkflowExecution):
        """Add logical dependencies between tasks."""
        
        task_list = list(workflow.tasks.values())
        
        # Simple dependency logic: analysis -> prediction -> reasoning
        for i in range(len(task_list) - 1):
            current_task = task_list[i]
            next_task = task_list[i + 1]
            
            # Add dependency edge
            workflow.dag.add_edge(current_task.task_id, next_task.task_id)
            next_task.dependencies.add(current_task.task_id)

class AgentOrchestrator:
    """Orchestrates the execution of workflow tasks across subsystems."""
    
    def __init__(self, connection, channel):
        self.logger = logging.getLogger("AGENT_ORCHESTRATOR")
        self.connection = connection
        self.channel = channel
        self.active_workflows: Dict[str, WorkflowExecution] = {}
        self.task_to_workflow: Dict[str, str] = {}
        
    def execute_workflow(self, workflow: WorkflowExecution):
        """Execute a designed workflow."""
        
        self.logger.info(f"Starting execution of workflow {workflow.workflow_id}")
        
        workflow.status = WorkflowStatus.EXECUTING
        workflow.started_at = datetime.utcnow()
        self.active_workflows[workflow.workflow_id] = workflow
        
        # Start with tasks that have no dependencies
        ready_tasks = self._get_ready_tasks(workflow)
        
        for task in ready_tasks:
            self._execute_task(task, workflow)
    
    def _get_ready_tasks(self, workflow: WorkflowExecution) -> List[TaskNode]:
        """Get tasks that are ready to execute (all dependencies completed)."""
        
        ready_tasks = []
        
        for task in workflow.tasks.values():
            if task.status == TaskStatus.PENDING:
                # Check if all dependencies are completed
                dependencies_met = all(
                    workflow.tasks[dep_id].status == TaskStatus.COMPLETED 
                    for dep_id in task.dependencies
                )
                
                if dependencies_met:
                    task.status = TaskStatus.READY
                    ready_tasks.append(task)
        
        return ready_tasks
    
    def _execute_task(self, task: TaskNode, workflow: WorkflowExecution):
        """Execute a single task by publishing to the appropriate queue."""
        
        self.logger.info(f"Executing task {task.task_id} on {task.subsystem}")
        
        task.status = TaskStatus.EXECUTING
        task.start_time = datetime.utcnow()
        
        # Map task to workflow for result tracking
        self.task_to_workflow[task.task_id] = workflow.workflow_id
        
        # Prepare task message
        task_message = {
            "task_id": task.task_id,
            "task_type": task.task_type,
            "payload": task.payload,
            "workflow_id": workflow.workflow_id,
            "timestamp": task.start_time.isoformat()
        }
        
        # Determine target queue based on subsystem
        queue_map = {
            "tetragnos": TETRAGNOS_QUEUE,
            "telos": TELOS_QUEUE,
            "thonoc": THONOC_QUEUE
        }
        
        target_queue = queue_map.get(task.subsystem)
        
        if not target_queue:
            self._handle_task_error(task, workflow, f"Unknown subsystem: {task.subsystem}")
            return
        
        try:
            # Publish task to worker queue
            self.channel.basic_publish(
                exchange='',
                routing_key=target_queue,
                body=json.dumps(task_message),
                properties=pika.BasicProperties(
                    delivery_mode=2,  # Make message persistent
                    correlation_id=task.task_id
                )
            )
            
            self.logger.info(f"Task {task.task_id} published to {target_queue}")
            
        except Exception as e:
            self._handle_task_error(task, workflow, f"Failed to publish task: {str(e)}")
    
    def handle_task_result(self, result_data: Dict[str, Any]):
        """Handle task completion result from workers."""
        
        task_id = result_data.get('task_id')
        workflow_id = self.task_to_workflow.get(task_id)
        
        if not workflow_id or workflow_id not in self.active_workflows:
            self.logger.warning(f"Received result for unknown task/workflow: {task_id}")
            return
        
        workflow = self.active_workflows[workflow_id]
        task = workflow.tasks.get(task_id)
        
        if not task:
            self.logger.warning(f"Task {task_id} not found in workflow {workflow_id}")
            return
        
        # Update task with result
        task.end_time = datetime.utcnow()
        task.result = result_data.get('result')
        
        if result_data.get('status') == 'success':
            task.status = TaskStatus.COMPLETED
            self.logger.info(f"Task {task_id} completed successfully")
            
            # Check if more tasks can be executed
            self._continue_workflow_execution(workflow)
            
        else:
            error_msg = result_data.get('error', 'Unknown error')
            self._handle_task_error(task, workflow, error_msg)
    
    def _handle_task_error(self, task: TaskNode, workflow: WorkflowExecution, error_msg: str):
        """Handle task execution error."""
        
        task.error = error_msg
        task.end_time = datetime.utcnow()
        
        if task.retry_count < task.max_retries:
            task.retry_count += 1
            task.status = TaskStatus.PENDING
            self.logger.warning(f"Task {task.task_id} failed, retrying ({task.retry_count}/{task.max_retries}): {error_msg}")
            
            # Retry the task
            self._execute_task(task, workflow)
        else:
            task.status = TaskStatus.FAILED
            self.logger.error(f"Task {task.task_id} failed permanently: {error_msg}")
            
            # Mark workflow as failed
            self._complete_workflow(workflow, WorkflowStatus.FAILED, error_msg)
    
    def _continue_workflow_execution(self, workflow: WorkflowExecution):
        """Continue workflow execution by starting ready tasks."""
        
        # Get newly ready tasks
        ready_tasks = self._get_ready_tasks(workflow)
        
        if ready_tasks:
            # Execute ready tasks
            for task in ready_tasks:
                self._execute_task(task, workflow)
        else:
            # Check if workflow is complete
            all_completed = all(
                task.status in [TaskStatus.COMPLETED, TaskStatus.FAILED] 
                for task in workflow.tasks.values()
            )
            
            if all_completed:
                # Check if any tasks failed
                failed_tasks = [task for task in workflow.tasks.values() if task.status == TaskStatus.FAILED]
                
                if failed_tasks:
                    error_msg = f"Workflow failed due to {len(failed_tasks)} failed tasks"
                    self._complete_workflow(workflow, WorkflowStatus.FAILED, error_msg)
                else:
                    # All tasks completed successfully
                    self._complete_workflow(workflow, WorkflowStatus.COMPLETED)
    
    def _complete_workflow(self, workflow: WorkflowExecution, status: WorkflowStatus, error_msg: str = None):
        """Complete workflow execution."""
        
        workflow.status = status
        workflow.completed_at = datetime.utcnow()
        workflow.error = error_msg
        
        if status == WorkflowStatus.COMPLETED:
            # Aggregate results from all tasks
            workflow.result = {
                "workflow_id": workflow.workflow_id,
                "goal": workflow.goal_description,
                "status": "completed",
                "task_results": {
                    task_id: task.result 
                    for task_id, task in workflow.tasks.items() 
                    if task.result
                },
                "execution_time": (workflow.completed_at - workflow.started_at).total_seconds(),
                "task_count": len(workflow.tasks)
            }
            
            self.logger.info(f"Workflow {workflow.workflow_id} completed successfully")
        else:
            self.logger.error(f"Workflow {workflow.workflow_id} failed: {error_msg}")
        
        # Clean up tracking
        for task_id in workflow.tasks.keys():
            self.task_to_workflow.pop(task_id, None)
        
        # Keep workflow in memory for a while for status queries
        # In production, this would be persisted to database

class ArchonNexus:
    """Main Archon Nexus service class."""
    
    def __init__(self):
        self.logger = logging.getLogger("ARCHON_NEXUS")
        self.connection = None
        self.channel = None
        self.validator = UnifiedFormalismValidator()
        self.workflow_architect = WorkflowArchitect(self.validator)
        self.agent_orchestrator = None
        self.shutdown_event = threading.Event()
        
        # Service state
        self.system_status = {
            'service_name': SERVICE_NAME,
            'status': 'initializing',
            'started_at': datetime.utcnow().isoformat(),
            'workflows_processed': 0,
            'active_workflows': 0,
            'last_activity': datetime.utcnow().isoformat()
        }
        
        # Setup signal handlers
        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)
        
    def _signal_handler(self, signum, frame):
        """Handle shutdown signals."""
        self.logger.info(f"Received signal {signum}, initiating shutdown...")
        self.shutdown_event.set()
    
    def _connect_rabbitmq(self) -> Tuple[pika.BlockingConnection, pika.channel.Channel]:
        """Establish RabbitMQ connection with retry logic."""
        
        max_retries = 10
        retry_delay = 5
        
        for attempt in range(max_retries):
            try:
                connection = pika.BlockingConnection(
                    pika.ConnectionParameters(
                        host=RABBITMQ_HOST,
                        port=RABBITMQ_PORT,
                        heartbeat=RABBITMQ_CONFIG.get('heartbeat', 600),
                        blocked_connection_timeout=300
                    )
                )
                channel = connection.channel()
                
                self.logger.info("Successfully connected to RabbitMQ")
                return connection, channel
                
            except pika.exceptions.AMQPConnectionError as e:
                self.logger.warning(f"RabbitMQ connection attempt {attempt + 1}/{max_retries} failed: {e}")
                if attempt < max_retries - 1:
                    time.sleep(retry_delay)
                else:
                    raise
    
    def _setup_queues(self):
        """Setup RabbitMQ queues for communication."""
        
        queues = [
            ARCHON_GOALS_QUEUE,
            TASK_RESULT_QUEUE,
            TETRAGNOS_QUEUE,
            TELOS_QUEUE,
            THONOC_QUEUE,
            DB_WRITE_QUEUE
        ]
        
        for queue in queues:
            self.channel.queue_declare(queue=queue, durable=True)
            self.logger.info(f"Queue '{queue}' declared")
    
    def _setup_consumers(self):
        """Setup message consumers."""
        
        # Consumer for goal requests
        self.channel.basic_qos(prefetch_count=1)
        self.channel.basic_consume(
            queue=ARCHON_GOALS_QUEUE,
            on_message_callback=self._handle_goal_message,
            auto_ack=False
        )
        
        # Consumer for task results
        self.channel.basic_consume(
            queue=TASK_RESULT_QUEUE,
            on_message_callback=self._handle_result_message,
            auto_ack=False
        )
        
        self.logger.info("Message consumers setup complete")
    
    def _handle_goal_message(self, ch, method, properties, body):
        """Handle incoming goal messages from Logos Nexus."""
        
        try:
            goal_data = json.loads(body.decode('utf-8'))
            goal_description = goal_data.get('query') or goal_data.get('goal')
            context = goal_data.get('context', {})
            
            self.logger.info(f"Received goal: {goal_description}")
            
            # Design workflow for the goal
            workflow = self.workflow_architect.design_workflow(goal_description, context)
            
            # Execute the workflow
            self.agent_orchestrator.execute_workflow(workflow)
            
            self.system_status['workflows_processed'] += 1
            self.system_status['active_workflows'] += 1
            self.system_status['last_activity'] = datetime.utcnow().isoformat()
            
            ch.basic_ack(delivery_tag=method.delivery_tag)
            
        except Exception as e:
            self.logger.error(f"Error processing goal message: {e}")
            ch.basic_nack(delivery_tag=method.delivery_tag, requeue=False)
    
    def _handle_result_message(self, ch, method, properties, body):
        """Handle task result messages from workers."""
        
        try:
            result_data = json.loads(body.decode('utf-8'))
            
            # Pass result to orchestrator
            self.agent_orchestrator.handle_task_result(result_data)
            
            # Update system status
            if result_data.get('workflow_completed'):
                self.system_status['active_workflows'] -= 1
            
            self.system_status['last_activity'] = datetime.utcnow().isoformat()
            
            ch.basic_ack(delivery_tag=method.delivery_tag)
            
        except Exception as e:
            self.logger.error(f"Error processing result message: {e}")
            ch.basic_nack(delivery_tag=method.delivery_tag, requeue=False)
    
    def start(self):
        """Start the Archon Nexus service."""
        
        self.logger.info("Starting Archon Nexus service...")
        
        try:
            # Connect to RabbitMQ
            self.connection, self.channel = self._connect_rabbitmq()
            
            # Initialize orchestrator
            self.agent_orchestrator = AgentOrchestrator(self.connection, self.channel)
            
            # Setup queues and consumers
            self._setup_queues()
            self._setup_consumers()
            
            self.system_status['status'] = 'running'
            self.logger.info("Archon Nexus service started successfully")
            
            # Start consuming messages
            self.logger.info("Waiting for messages. To exit press CTRL+C")
            
            while not self.shutdown_event.is_set():
                try:
                    self.connection.process_data_events(time_limit=1)
                except KeyboardInterrupt:
                    break
                except Exception as e:
                    self.logger.error(f"Error in main loop: {e}")
                    time.sleep(1)
            
        except Exception as e:
            self.logger.error(f"Error starting service: {e}")
            self.system_status['status'] = 'error'
            raise
        finally:
            self.stop()
    
    def stop(self):
        """Stop the Archon Nexus service."""
        
        self.logger.info("Stopping Archon Nexus service...")
        
        self.system_status['status'] = 'stopping'
        
        if self.connection and not self.connection.is_closed:
            self.connection.close()
        
        self.system_status['status'] = 'stopped'
        self.logger.info("Archon Nexus service stopped")

def main():
    """Main entry point."""
    service = ArchonNexus()
    
    try:
        service.start()
    except KeyboardInterrupt:
        service.logger.info("Service interrupted by user")
    except Exception as e:
        service.logger.error(f"Service failed: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()