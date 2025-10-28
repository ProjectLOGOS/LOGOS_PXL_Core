# --- START OF FILE core/data_structures.py ---

#!/usr/bin/env python3
"""
Core Data Structures for LOGOS AGI
Fundamental data types and structures used throughout the system

File: core/data_structures.py
Author: LOGOS AGI Development Team
Version: 2.0.0
Date: 2025-01-28
"""

import hashlib
import json
import time
import uuid
from dataclasses import dataclass, field
from enum import Enum
from typing import Any

# =========================================================================
# I. FOUNDATIONAL ENUMS
# =========================================================================


class SystemState(Enum):
    """Overall system operational states"""

    INITIALIZING = "initializing"
    OPERATIONAL = "operational"
    DEGRADED = "degraded"
    ERROR = "error"
    SHUTDOWN = "shutdown"


class ProcessingPriority(Enum):
    """Processing priority levels"""

    LOW = 1
    NORMAL = 2
    HIGH = 3
    CRITICAL = 4
    EMERGENCY = 5


class ValidationStatus(Enum):
    """Validation status for operations"""

    PENDING = "pending"
    VALIDATED = "validated"
    REJECTED = "rejected"
    ERROR = "error"


class SubsystemType(Enum):
    """Types of subsystems in LOGOS architecture"""

    LOGOS = "logos"  # Central orchestrator
    TETRAGNOS = "tetragnos"  # Pattern recognizer
    TELOS = "telos"  # Scientist/causal reasoner
    THONOC = "thonoc"  # Logician


class QueryType(Enum):
    """Types of queries that can be processed"""

    GENERAL = "general"
    LOGICAL = "logical"
    CAUSAL = "causal"
    CREATIVE = "creative"
    ANALYTICAL = "analytical"
    THEOLOGICAL = "theological"
    MATHEMATICAL = "mathematical"


# =========================================================================
# II. CORE MESSAGING STRUCTURES
# =========================================================================


@dataclass
class SystemMessage:
    """Base message structure for inter-service communication"""

    message_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    message_type: str = ""
    source_service: str = ""
    target_service: str = ""
    timestamp: float = field(default_factory=time.time)
    payload: dict[str, Any] = field(default_factory=dict)
    correlation_id: str | None = None
    priority: ProcessingPriority = ProcessingPriority.NORMAL

    def to_dict(self) -> dict[str, Any]:
        """Convert to dictionary for serialization"""
        return {
            "message_id": self.message_id,
            "message_type": self.message_type,
            "source_service": self.source_service,
            "target_service": self.target_service,
            "timestamp": self.timestamp,
            "payload": self.payload,
            "correlation_id": self.correlation_id,
            "priority": self.priority.value,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "SystemMessage":
        """Create from dictionary"""
        return cls(
            message_id=data.get("message_id", str(uuid.uuid4())),
            message_type=data.get("message_type", ""),
            source_service=data.get("source_service", ""),
            target_service=data.get("target_service", ""),
            timestamp=data.get("timestamp", time.time()),
            payload=data.get("payload", {}),
            correlation_id=data.get("correlation_id"),
            priority=ProcessingPriority(data.get("priority", ProcessingPriority.NORMAL.value)),
        )


@dataclass
class OperationResult:
    """Result of a system operation"""

    operation_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    success: bool = False
    result_data: Any = None
    error_message: str | None = None
    execution_time: float = 0.0
    timestamp: float = field(default_factory=time.time)
    metadata: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        """Convert to dictionary for serialization"""
        return {
            "operation_id": self.operation_id,
            "success": self.success,
            "result_data": self.result_data,
            "error_message": self.error_message,
            "execution_time": self.execution_time,
            "timestamp": self.timestamp,
            "metadata": self.metadata,
        }


@dataclass
class ValidationToken:
    """Token for operation validation"""

    token_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    operation_data: dict[str, Any] = field(default_factory=dict)
    status: ValidationStatus = ValidationStatus.PENDING
    created_at: float = field(default_factory=time.time)
    validated_at: float | None = None
    validated_by: str | None = None
    validation_data: dict[str, Any] = field(default_factory=dict)

    def validate(self, validator_id: str):
        """Mark token as validated"""
        self.status = ValidationStatus.VALIDATED
        self.validated_by = validator_id
        self.validated_at = time.time()

    def reject(self, reason: str):
        """Mark token as rejected"""
        self.status = ValidationStatus.REJECTED
        self.validation_data["rejection_reason"] = reason
        self.validated_at = time.time()


@dataclass
class TaskDescriptor:
    """Descriptor for computational tasks"""

    task_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    task_type: str = ""
    description: str = ""
    input_data: Any = None
    parameters: dict[str, Any] = field(default_factory=dict)
    priority: ProcessingPriority = ProcessingPriority.NORMAL
    created_at: float = field(default_factory=time.time)
    assigned_to: str | None = None
    dependencies: list[str] = field(default_factory=list)
    estimated_duration: float | None = None

    def add_dependency(self, task_id: str):
        """Add dependency on another task"""
        if task_id not in self.dependencies:
            self.dependencies.append(task_id)

    def can_execute(self, completed_tasks: set) -> bool:
        """Check if task can execute given completed dependencies"""
        return all(dep_id in completed_tasks for dep_id in self.dependencies)


@dataclass
class SystemMetrics:
    """System performance and health metrics"""

    component_name: str
    timestamp: float = field(default_factory=time.time)
    cpu_usage: float = 0.0
    memory_usage: float = 0.0
    operations_per_second: float = 0.0
    error_rate: float = 0.0
    response_time: float = 0.0
    custom_metrics: dict[str, float] = field(default_factory=dict)

    def add_metric(self, name: str, value: float):
        """Add custom metric"""
        self.custom_metrics[name] = value

    def to_summary(self) -> dict[str, Any]:
        """Convert to summary dictionary"""
        return {
            "component": self.component_name,
            "timestamp": self.timestamp,
            "performance": {
                "cpu_usage": self.cpu_usage,
                "memory_usage": self.memory_usage,
                "ops_per_second": self.operations_per_second,
                "response_time": self.response_time,
            },
            "health": {
                "error_rate": self.error_rate,
                "status": "healthy" if self.error_rate < 0.05 else "degraded",
            },
            "custom": self.custom_metrics,
        }


# =========================================================================
# III. LOGOS-SPECIFIC DATA STRUCTURES
# =========================================================================


@dataclass
class LogosQuery:
    """Standard query format for LOGOS system"""

    query_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    query_text: str = ""
    query_type: QueryType = QueryType.GENERAL
    context: dict[str, Any] = field(default_factory=dict)
    requester_id: str = ""
    created_at: float = field(default_factory=time.time)
    priority: ProcessingPriority = ProcessingPriority.NORMAL
    timeout: float = 30.0
    metadata: dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> dict[str, Any]:
        """Convert to dictionary for serialization"""
        return {
            "query_id": self.query_id,
            "query_text": self.query_text,
            "query_type": self.query_type.value,
            "context": self.context,
            "requester_id": self.requester_id,
            "created_at": self.created_at,
            "priority": self.priority.value,
            "timeout": self.timeout,
            "metadata": self.metadata,
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> "LogosQuery":
        """Create from dictionary"""
        return cls(
            query_id=data.get("query_id", str(uuid.uuid4())),
            query_text=data.get("query_text", ""),
            query_type=QueryType(data.get("query_type", QueryType.GENERAL.value)),
            context=data.get("context", {}),
            requester_id=data.get("requester_id", ""),
            created_at=data.get("created_at", time.time()),
            priority=ProcessingPriority(data.get("priority", ProcessingPriority.NORMAL.value)),
            timeout=data.get("timeout", 30.0),
            metadata=data.get("metadata", {}),
        )


@dataclass
class SubsystemStatus:
    """Status information for a subsystem"""

    subsystem_type: SubsystemType
    state: SystemState = SystemState.INITIALIZING
    last_heartbeat: float = field(default_factory=time.time)
    active_tasks: int = 0
    completed_tasks: int = 0
    error_count: int = 0
    metrics: SystemMetrics | None = None
    capabilities: list[str] = field(default_factory=list)

    def is_healthy(self) -> bool:
        """Check if subsystem is healthy"""
        time_since_heartbeat = time.time() - self.last_heartbeat
        return (
            self.state == SystemState.OPERATIONAL
            and time_since_heartbeat < 60.0  # Within last minute
        )

    def update_heartbeat(self):
        """Update heartbeat timestamp"""
        self.last_heartbeat = time.time()


@dataclass
class KnowledgeItem:
    """Structured knowledge item"""

    item_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    content: str = ""
    item_type: str = "fact"  # fact, rule, principle, theorem, etc.
    domain: str = "general"
    confidence: float = 1.0
    source: str = ""
    created_at: float = field(default_factory=time.time)
    tags: list[str] = field(default_factory=list)
    relationships: dict[str, list[str]] = field(default_factory=dict)

    def add_relationship(self, relationship_type: str, related_item_id: str):
        """Add relationship to another knowledge item"""
        if relationship_type not in self.relationships:
            self.relationships[relationship_type] = []
        if related_item_id not in self.relationships[relationship_type]:
            self.relationships[relationship_type].append(related_item_id)


# =========================================================================
# IV. TRINITY-SPECIFIC DATA STRUCTURES
# =========================================================================


@dataclass
class TrinityVector:
    """Three-dimensional vector for Trinity operations"""

    existence: float = 0.0
    goodness: float = 0.0
    truth: float = 0.0

    def __post_init__(self):
        """Normalize vector to unit sphere"""
        magnitude = self.magnitude()
        if magnitude > 1e-10:
            self.existence /= magnitude
            self.goodness /= magnitude
            self.truth /= magnitude

    def magnitude(self) -> float:
        """Calculate vector magnitude"""
        return (self.existence**2 + self.goodness**2 + self.truth**2) ** 0.5

    def trinity_product(self) -> float:
        """Calculate Trinity product: E × G × T"""
        return abs(self.existence * self.goodness * self.truth)

    def dot_product(self, other: "TrinityVector") -> float:
        """Calculate dot product with another Trinity vector"""
        return (
            self.existence * other.existence
            + self.goodness * other.goodness
            + self.truth * other.truth
        )

    def to_tuple(self) -> tuple[float, float, float]:
        """Convert to tuple"""
        return (self.existence, self.goodness, self.truth)


@dataclass
class FractalPosition:
    """Position in fractal space"""

    real: float = 0.0
    imaginary: float = 0.0
    dimension: float = 2.0
    iteration_count: int = 0
    converged: bool = False

    def to_complex(self) -> complex:
        """Convert to complex number"""
        return complex(self.real, self.imaginary)

    def distance_from_origin(self) -> float:
        """Calculate distance from origin"""
        return (self.real**2 + self.imaginary**2) ** 0.5


# =========================================================================
# V. WORKFLOW STRUCTURES
# =========================================================================


@dataclass
class WorkflowStep:
    """Single step in a workflow"""

    step_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    step_name: str = ""
    step_type: str = ""
    input_requirements: list[str] = field(default_factory=list)
    output_specification: dict[str, Any] = field(default_factory=dict)
    parameters: dict[str, Any] = field(default_factory=dict)
    dependencies: list[str] = field(default_factory=list)
    assigned_subsystem: SubsystemType | None = None
    estimated_duration: float = 0.0

    def can_execute(self, completed_steps: set) -> bool:
        """Check if step can execute"""
        return all(dep in completed_steps for dep in self.dependencies)


@dataclass
class Workflow:
    """Complete workflow definition"""

    workflow_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    name: str = ""
    description: str = ""
    steps: list[WorkflowStep] = field(default_factory=list)
    created_at: float = field(default_factory=time.time)
    created_by: str = ""
    version: str = "1.0"

    def add_step(self, step: WorkflowStep):
        """Add step to workflow"""
        self.steps.append(step)

    def get_ready_steps(self, completed_steps: set) -> list[WorkflowStep]:
        """Get steps that are ready to execute"""
        return [step for step in self.steps if step.can_execute(completed_steps)]


@dataclass
class EventNotification:
    """System event notification"""

    event_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    event_type: str = ""
    source: str = ""
    timestamp: float = field(default_factory=time.time)
    data: dict[str, Any] = field(default_factory=dict)
    severity: str = "info"  # debug, info, warning, error, critical
    tags: list[str] = field(default_factory=list)


# =========================================================================
# VI. UTILITY FUNCTIONS
# =========================================================================


def generate_secure_hash(data: Any) -> str:
    """Generate secure hash of data"""
    if isinstance(data, dict):
        data_str = json.dumps(data, sort_keys=True)
    else:
        data_str = str(data)

    return hashlib.sha256(data_str.encode()).hexdigest()


def create_correlation_id() -> str:
    """Create correlation ID for tracking related operations"""
    return f"corr_{int(time.time())}_{str(uuid.uuid4())[:8]}"


def validate_json_schema(
    data: dict[str, Any], required_fields: list[str]
) -> tuple[bool, list[str]]:
    """Validate JSON data against required schema"""
    missing_fields = []

    for field in required_fields:
        if field not in data:
            missing_fields.append(field)

    return len(missing_fields) == 0, missing_fields


def serialize_for_transmission(obj: Any) -> str:
    """Serialize object for network transmission"""
    if hasattr(obj, "to_dict"):
        return json.dumps(obj.to_dict())
    elif isinstance(obj, (dict, list, str, int, float, bool)):
        return json.dumps(obj)
    else:
        return json.dumps(str(obj))


def deserialize_from_transmission(data: str, target_type: type = dict) -> Any:
    """Deserialize object from network transmission"""
    try:
        parsed_data = json.loads(data)

        if target_type == dict:
            return parsed_data
        elif hasattr(target_type, "from_dict") and isinstance(parsed_data, dict):
            return target_type.from_dict(parsed_data)
        else:
            return parsed_data
    except json.JSONDecodeError:
        return None


# =========================================================================
# VII. MODULE EXPORTS
# =========================================================================

__all__ = [
    # Enums
    "SystemState",
    "ProcessingPriority",
    "ValidationStatus",
    "SubsystemType",
    "QueryType",
    # Core data structures
    "SystemMessage",
    "OperationResult",
    "ValidationToken",
    "TaskDescriptor",
    "SystemMetrics",
    # LOGOS-specific structures
    "LogosQuery",
    "SubsystemStatus",
    "KnowledgeItem",
    # Trinity structures
    "TrinityVector",
    "FractalPosition",
    # Workflow structures
    "WorkflowStep",
    "Workflow",
    "EventNotification",
    # Utility functions
    "generate_secure_hash",
    "create_correlation_id",
    "validate_json_schema",
    "serialize_for_transmission",
    "deserialize_from_transmission",
]

# --- END OF FILE core/data_structures.py ---
