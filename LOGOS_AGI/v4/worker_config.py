# logos_agi_v1/shared/worker_config.py

"""
Shared configuration for all LOGOS AGI worker subsystems.
Provides common settings, queue configurations, and utility functions.
"""

import os
from typing import Dict, Any, List
from dataclasses import dataclass
from enum import Enum

class WorkerType(Enum):
    """Enumeration of worker subsystem types."""
    TETRAGNOS = "tetragnos"
    TELOS = "telos"
    THONOC = "thonoc"

class TaskPriority(Enum):
    """Task priority levels."""
    LOW = 1
    MEDIUM = 2
    HIGH = 3
    CRITICAL = 4

@dataclass
class QueueConfig:
    """Configuration for RabbitMQ queues."""
    name: str
    durable: bool = True
    auto_delete: bool = False
    max_length: int = 10000
    message_ttl: int = 3600000  # 1 hour in milliseconds

@dataclass
class WorkerConfig:
    """Base configuration for worker subsystems."""
    worker_type: WorkerType
    task_queue: QueueConfig
    result_queue: QueueConfig
    heartbeat_interval: int = 30
    max_retries: int = 3
    processing_timeout: int = 300  # 5 minutes
    log_level: str = "INFO"

# RabbitMQ Configuration
RABBITMQ_CONFIG = {
    'host': os.getenv('RABBITMQ_HOST', 'rabbitmq'),
    'port': int(os.getenv('RABBITMQ_PORT', '5672')),
    'username': os.getenv('RABBITMQ_USER', 'guest'),
    'password': os.getenv('RABBITMQ_PASS', 'guest'),
    'virtual_host': os.getenv('RABBITMQ_VHOST', '/'),
    'heartbeat': int(os.getenv('RABBITMQ_HEARTBEAT', '600')),
    'blocked_connection_timeout': int(os.getenv('RABBITMQ_BLOCKED_TIMEOUT', '300')),
    'connection_attempts': int(os.getenv('RABBITMQ_CONNECTION_ATTEMPTS', '10')),
    'retry_delay': int(os.getenv('RABBITMQ_RETRY_DELAY', '5')),
}

# Queue Configurations
QUEUE_CONFIGS = {
    WorkerType.TETRAGNOS: WorkerConfig(
        worker_type=WorkerType.TETRAGNOS,
        task_queue=QueueConfig('tetragnos_task_queue'),
        result_queue=QueueConfig('task_result_queue'),
        processing_timeout=180  # 3 minutes for NLP tasks
    ),
    WorkerType.TELOS: WorkerConfig(
        worker_type=WorkerType.TELOS,
        task_queue=QueueConfig('telos_task_queue'),
        result_queue=QueueConfig('task_result_queue'),
        processing_timeout=300  # 5 minutes for scientific computation
    ),
    WorkerType.THONOC: WorkerConfig(
        worker_type=WorkerType.THONOC,
        task_queue=QueueConfig('thonoc_task_queue'),
        result_queue=QueueConfig('task_result_queue'),
        processing_timeout=600  # 10 minutes for theorem proving
    )
}

# Logging Configuration
LOGGING_CONFIG = {
    'version': 1,
    'disable_existing_loggers': False,
    'formatters': {
        'standard': {
            'format': '%(asctime)s - %(levelname)s - %(name)s - %(message)s'
        },
        'detailed': {
            'format': '%(asctime)s - %(levelname)s - %(name)s - %(funcName)s:%(lineno)d - %(message)s'
        }
    },
    'handlers': {
        'console': {
            'class': 'logging.StreamHandler',
            'level': 'INFO',
            'formatter': 'standard',
            'stream': 'ext://sys.stdout'
        },
        'file': {
            'class': 'logging.FileHandler',
            'level': 'DEBUG',
            'formatter': 'detailed',
            'filename': '/app/logs/worker.log',
            'mode': 'a'
        }
    },
    'loggers': {
        '': {  # Root logger
            'handlers': ['console', 'file'],
            'level': 'DEBUG',
            'propagate': False
        }
    }
}

# Performance Configuration
PERFORMANCE_CONFIG = {
    'max_concurrent_tasks': int(os.getenv('MAX_CONCURRENT_TASKS', '10')),
    'memory_limit_mb': int(os.getenv('MEMORY_LIMIT_MB', '2048')),
    'cpu_limit_cores': int(os.getenv('CPU_LIMIT_CORES', '2')),
    'cache_size_mb': int(os.getenv('CACHE_SIZE_MB', '512')),
    'batch_size': int(os.getenv('BATCH_SIZE', '32')),
    'prefetch_count': int(os.getenv('PREFETCH_COUNT', '1'))
}

# Security Configuration
SECURITY_CONFIG = {
    'enable_encryption': os.getenv('ENABLE_ENCRYPTION', 'false').lower() == 'true',
    'max_message_size_mb': int(os.getenv('MAX_MESSAGE_SIZE_MB', '10')),
    'allowed_content_types': ['application/json', 'text/plain'],
    'rate_limit_per_minute': int(os.getenv('RATE_LIMIT_PER_MINUTE', '1000')),
    'enable_audit_logging': os.getenv('ENABLE_AUDIT_LOGGING', 'true').lower() == 'true'
}

# Task Type Mappings
TASK_TYPE_MAPPINGS = {
    WorkerType.TETRAGNOS: [
        'cluster_texts',
        'translate_text',
        'extract_features',
        'analyze_patterns',
        'semantic_similarity'
    ],
    WorkerType.TELOS: [
        'predict_outcomes',
        'causal_retrodiction',
        'analyze_intervention',
        'forecast_series',
        'test_hypothesis',
        'build_causal_model'
    ],
    WorkerType.THONOC: [
        'construct_proof',
        'assign_consequence',
        'evaluate_lambda',
        'modal_reasoning',
        'consistency_check',
        'theorem_proving'
    ]
}

def get_worker_config(worker_type: WorkerType) -> WorkerConfig:
    """Get configuration for a specific worker type."""
    return QUEUE_CONFIGS.get(worker_type)

def get_supported_tasks(worker_type: WorkerType) -> List[str]:
    """Get list of supported task types for a worker."""
    return TASK_TYPE_MAPPINGS.get(worker_type, [])

def validate_task_type(worker_type: WorkerType, task_type: str) -> bool:
    """Validate if a task type is supported by a worker."""
    supported_tasks = get_supported_tasks(worker_type)
    return task_type in supported_tasks

def get_queue_name(worker_type: WorkerType, queue_type: str = 'task') -> str:
    """Get queue name for a worker type."""
    config = get_worker_config(worker_type)
    if not config:
        return None

    if queue_type == 'task':
        return config.task_queue.name
    elif queue_type == 'result':
        return config.result_queue.name
    else:
        return None

def create_task_message(task_id: str, task_type: str, payload: Dict[str, Any],
                       priority: TaskPriority = TaskPriority.MEDIUM,
                       workflow_id: str = None) -> Dict[str, Any]:
    """Create a standardized task message."""
    return {
        'task_id': task_id,
        'task_type': task_type,
        'type': task_type,  # Alias for backward compatibility
        'payload': payload,
        'priority': priority.value,
        'workflow_id': workflow_id,
        'created_at': os.getenv('TASK_TIMESTAMP'),
        'timeout': PERFORMANCE_CONFIG['processing_timeout']
    }

def create_result_message(subsystem: str, task_id: str, status: str,
                         result: Dict[str, Any], processing_time: float = None,
                         workflow_id: str = None) -> Dict[str, Any]:
    """Create a standardized result message."""
    return {
        'subsystem': subsystem,
        'task_id': task_id,
        'workflow_id': workflow_id,
        'status': status,
        'result': result,
        'processing_time': processing_time,
        'timestamp': os.getenv('RESULT_TIMESTAMP')
    }

# Environment-specific overrides
if os.getenv('ENVIRONMENT') == 'development':
    PERFORMANCE_CONFIG['max_concurrent_tasks'] = 5
    LOGGING_CONFIG['handlers']['console']['level'] = 'DEBUG'

elif os.getenv('ENVIRONMENT') == 'production':
    PERFORMANCE_CONFIG['max_concurrent_tasks'] = 20
    LOGGING_CONFIG['handlers']['console']['level'] = 'INFO'
    SECURITY_CONFIG['enable_encryption'] = True

# Validation function
def validate_config() -> bool:
    """Validate configuration settings."""
    try:
        # Check required environment variables
        required_vars = ['RABBITMQ_HOST']
        for var in required_vars:
            if not os.getenv(var):
                print(f"Warning: Required environment variable {var} not set")

        # Validate queue configurations
        for worker_type, config in QUEUE_CONFIGS.items():
            if not config.task_queue.name or not config.result_queue.name:
                print(f"Error: Invalid queue configuration for {worker_type}")
                return False

        # Validate performance limits
        if PERFORMANCE_CONFIG['max_concurrent_tasks'] < 1:
            print("Error: max_concurrent_tasks must be at least 1")
            return False

        return True

    except Exception as e:
        print(f"Configuration validation error: {e}")
        return False

if __name__ == '__main__':
    # Configuration test
    if validate_config():
        print("✓ Configuration validation passed")
        for worker_type in WorkerType:
            config = get_worker_config(worker_type)
            tasks = get_supported_tasks(worker_type)
            print(f"✓ {worker_type.value}: {len(tasks)} supported tasks")
    else:
        print("✗ Configuration validation failed")
        exit(1)
