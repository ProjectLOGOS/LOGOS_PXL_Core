"""
Enhanced Reference Monitor - Runtime Safety and Introspection System

This module wraps all reasoning evaluation calls with comprehensive validation,
logging, and anomaly detection to ensure safe autonomous operation.
"""

import json
import time
import logging
import hashlib
import threading
import uuid
from datetime import datetime
from pathlib import Path
from typing import Dict, Any, List, Optional, Union, Callable, Tuple
from contextlib import contextmanager
from dataclasses import dataclass, asdict
from collections import defaultdict, deque
import os
import sys

# Add runtime path for imports
sys.path.append(str(Path(__file__).parent))

from runtime.iel_runtime_interface import (
    ModalLogicEvaluator, IELEvaluator, ProofBridgeError
)

logger = logging.getLogger(__name__)

@dataclass
class EvaluationRecord:
    """Complete record of a logic evaluation"""
    evaluation_id: str
    timestamp: float
    evaluator_type: str
    operation: str
    input_data: Dict[str, Any]
    output_data: Dict[str, Any]
    success: bool
    error_message: Optional[str]
    execution_time_ms: float
    metadata: Dict[str, Any]
    anomaly_flags: List[str]
    consistency_check: bool

class MonitoringState:
    """Thread-safe state tracking for the reference monitor"""

    def __init__(self):
        self._lock = threading.RLock()
        self.evaluation_count = 0
        self.error_count = 0
        self.anomaly_count = 0
        self.recent_evaluations = deque(maxlen=1000)
        self.error_patterns = defaultdict(int)
        self.blocked_operations = set()
        self.warning_conditions = set()

class ConsistencyValidator:
    """Validates logical consistency of evaluations"""

    def __init__(self):
        self.known_contradictions = set()
        self.tautology_cache = {}

    def validate_proposition_consistency(self, proposition: str, result: bool,
                                       context: Dict[str, Any]) -> Tuple[bool, List[str]]:
        """
        Check if the evaluation result is logically consistent

        Returns:
            (is_consistent, list_of_issues)
        """
        issues = []

        # Check for obvious contradictions
        if self._is_contradiction(proposition):
            if result:
                issues.append(f"Contradiction evaluated as True: {proposition}")

        # Check for obvious tautologies
        if self._is_tautology(proposition):
            if not result:
                issues.append(f"Tautology evaluated as False: {proposition}")

        # Check modal logic axioms
        modal_issues = self._check_modal_axioms(proposition, result, context)
        issues.extend(modal_issues)

        return len(issues) == 0, issues

    def _is_contradiction(self, proposition: str) -> bool:
        """Check if proposition is obviously contradictory"""
        # Simple contradiction patterns
        contradiction_patterns = [
            "p && ~p",
            "q && ~q",
            "false",
            "⊥"
        ]
        return any(pattern in proposition.lower() for pattern in contradiction_patterns)

    def _is_tautology(self, proposition: str) -> bool:
        """Check if proposition is obviously tautological"""
        tautology_patterns = [
            "p || ~p",
            "q || ~q",
            "true",
            "⊤"
        ]
        return any(pattern in proposition.lower() for pattern in tautology_patterns)

    def _check_modal_axioms(self, proposition: str, result: bool,
                           context: Dict[str, Any]) -> List[str]:
        """Check compliance with modal logic axioms"""
        issues = []

        # T axiom: []p -> p
        if "[]" in proposition and "->" in proposition:
            if "[]p -> p" in proposition.replace(" ", "") and not result:
                issues.append("T axiom violation: []p -> p should be valid")

        # K axiom: [](p -> q) -> ([]p -> []q)
        if "[](p -> q) -> ([]p -> []q)" in proposition.replace(" ", "") and not result:
            issues.append("K axiom violation: distribution should be valid")

        return issues

class AnomalyDetector:
    """Detects anomalous patterns in evaluation behavior"""

    def __init__(self):
        self.baseline_metrics = {}
        self.alert_thresholds = {
            'error_rate': 0.1,  # 10% error rate triggers alert
            'avg_time_multiplier': 5.0,  # 5x normal time triggers alert
            'contradiction_rate': 0.05,  # 5% contradictions triggers alert
        }

    def analyze_evaluation(self, record: EvaluationRecord,
                          recent_history: List[EvaluationRecord]) -> List[str]:
        """
        Analyze evaluation for anomalous patterns

        Returns:
            List of anomaly descriptions
        """
        anomalies = []

        # Check execution time anomaly
        if self._is_time_anomaly(record, recent_history):
            anomalies.append("execution_time_anomaly")

        # Check error rate anomaly
        if self._is_error_rate_anomaly(recent_history):
            anomalies.append("high_error_rate")

        # Check contradiction pattern
        if self._is_contradiction_anomaly(record):
            anomalies.append("logical_contradiction")

        # Check input complexity anomaly
        if self._is_complexity_anomaly(record):
            anomalies.append("input_complexity_anomaly")

        return anomalies

    def _is_time_anomaly(self, record: EvaluationRecord,
                        history: List[EvaluationRecord]) -> bool:
        """Check if execution time is anomalously high"""
        if len(history) < 10:
            return False

        recent_times = [r.execution_time_ms for r in history[-20:] if r.success]
        if not recent_times:
            return False

        avg_time = sum(recent_times) / len(recent_times)
        threshold = avg_time * self.alert_thresholds['avg_time_multiplier']

        return record.execution_time_ms > threshold

    def _is_error_rate_anomaly(self, history: List[EvaluationRecord]) -> bool:
        """Check if recent error rate is anomalously high"""
        if len(history) < 20:
            return False

        recent_errors = sum(1 for r in history[-20:] if not r.success)
        error_rate = recent_errors / 20

        return error_rate > self.alert_thresholds['error_rate']

    def _is_contradiction_anomaly(self, record: EvaluationRecord) -> bool:
        """Check if evaluation result represents a logical contradiction"""
        return 'logical_contradiction' in record.anomaly_flags

    def _is_complexity_anomaly(self, record: EvaluationRecord) -> bool:
        """Check if input complexity is unusually high"""
        input_str = str(record.input_data)
        # Simple complexity heuristics
        return (len(input_str) > 1000 or
                input_str.count('(') > 50 or
                input_str.count('&&') + input_str.count('||') > 20)

class EnhancedReferenceMonitor:
    """
    Enhanced Reference Monitor with comprehensive validation and anomaly detection

    Wraps all IEL runtime interface calls with:
    - Pre-evaluation validation
    - Post-evaluation consistency checking
    - Comprehensive logging
    - Anomaly detection and alerting
    - Safety circuit breakers
    """

    def __init__(self, config: Optional[Dict[str, Any]] = None):
        self.config = config or self._load_default_config()
        self.state = MonitoringState()
        self.consistency_validator = ConsistencyValidator()
        self.anomaly_detector = AnomalyDetector()

        # Initialize logging
        self._setup_logging()

        # Initialize wrapped evaluators
        self.modal_evaluator = ModalLogicEvaluator()
        self.iel_evaluator = IELEvaluator()

        # Safety settings
        self.max_errors_per_minute = self.config.get('max_errors_per_minute', 10)
        self.enable_circuit_breaker = self.config.get('enable_circuit_breaker', True)
        self.emergency_halt = False

        logger.info("Enhanced Reference Monitor initialized")

    def _load_default_config(self) -> Dict[str, Any]:
        """Load default configuration"""
        return {
            'log_level': 'INFO',
            'telemetry_file': 'logs/monitor_telemetry.jsonl',
            'max_errors_per_minute': 10,
            'enable_circuit_breaker': True,
            'enable_anomaly_detection': True,
            'enable_consistency_validation': True,
            'audit_directory': 'audit/',
        }

    def _setup_logging(self):
        """Setup structured logging for telemetry"""
        log_dir = Path(self.config['telemetry_file']).parent
        log_dir.mkdir(exist_ok=True)

        # Configure logger
        log_level = getattr(logging, self.config['log_level'])
        logging.basicConfig(level=log_level)

        # Create telemetry file handler
        self.telemetry_handler = logging.FileHandler(
            self.config['telemetry_file'], mode='a'
        )
        self.telemetry_handler.setFormatter(
            logging.Formatter('%(message)s')  # Raw JSON
        )

    def _log_evaluation(self, record: EvaluationRecord):
        """Log evaluation record to telemetry file"""
        telemetry_entry = {
            'timestamp': datetime.fromtimestamp(record.timestamp).isoformat(),
            'evaluation_record': asdict(record)
        }

        self.telemetry_handler.emit(
            logging.LogRecord(
                name='telemetry',
                level=logging.INFO,
                pathname='',
                lineno=0,
                msg=json.dumps(telemetry_entry),
                args=(),
                exc_info=None
            )
        )

    def _pre_evaluation_validation(self, operation: str, **kwargs) -> Tuple[bool, List[str]]:
        """
        Validate inputs before evaluation

        Returns:
            (is_valid, list_of_issues)
        """
        issues = []

        # Check if system is in emergency halt
        if self.emergency_halt:
            issues.append("System in emergency halt state")
            return False, issues

        # Check if operation is blocked
        if operation in self.state.blocked_operations:
            issues.append(f"Operation {operation} is blocked")

        # Validate proposition syntax
        proposition = kwargs.get('proposition')
        if proposition:
            syntax_issues = self._validate_syntax(proposition)
            issues.extend(syntax_issues)

        # Check operator scope
        scope_issues = self._validate_operator_scope(**kwargs)
        issues.extend(scope_issues)

        # Check allowed constructs
        construct_issues = self._validate_allowed_constructs(**kwargs)
        issues.extend(construct_issues)

        return len(issues) == 0, issues

    def _validate_syntax(self, proposition: str) -> List[str]:
        """Validate proposition syntax"""
        issues = []

        # Check balanced parentheses
        if proposition.count('(') != proposition.count(')'):
            issues.append("Unbalanced parentheses")

        # Check for dangerous patterns
        dangerous_patterns = ['__import__', 'eval', 'exec', 'os.system']
        for pattern in dangerous_patterns:
            if pattern in proposition:
                issues.append(f"Dangerous pattern detected: {pattern}")

        # Check length limits
        if len(proposition) > 5000:
            issues.append("Proposition too long (>5000 chars)")

        return issues

    def _validate_operator_scope(self, **kwargs) -> List[str]:
        """Validate that operators are used within allowed scope"""
        issues = []

        # Check modal operator nesting depth
        proposition = kwargs.get('proposition', '')
        box_depth = self._count_nested_operators(proposition, '[]')
        diamond_depth = self._count_nested_operators(proposition, '<>')

        if box_depth > 10:
            issues.append(f"Box operator nesting too deep: {box_depth}")
        if diamond_depth > 10:
            issues.append(f"Diamond operator nesting too deep: {diamond_depth}")

        return issues

    def _count_nested_operators(self, proposition: str, operator: str) -> int:
        """Count maximum nesting depth of an operator"""
        max_depth = 0
        current_depth = 0

        i = 0
        while i < len(proposition):
            if proposition[i:i+len(operator)] == operator:
                current_depth += 1
                max_depth = max(max_depth, current_depth)
                i += len(operator)
            elif operator == '[]' and proposition[i] == ']':
                current_depth = max(0, current_depth - 1)
                i += 1
            elif operator == '<>' and proposition[i] == '>':
                current_depth = max(0, current_depth - 1)
                i += 1
            else:
                i += 1

        return max_depth

    def _validate_allowed_constructs(self, **kwargs) -> List[str]:
        """Validate that only allowed logical constructs are used"""
        issues = []

        proposition = kwargs.get('proposition', '')

        # Define allowed constructs
        allowed_operators = {
            '&&', '||', '~', '->', '<->',
            '[]', '<>', 'I(', 'E(',
            '(', ')', 'true', 'false'
        }

        # Check for disallowed constructs (simple heuristic)
        if any(char in proposition for char in ['$', '@', '#', '&', '|']
               if '&&' not in proposition and '||' not in proposition):
            issues.append("Disallowed characters detected")

        return issues

    def _post_evaluation_validation(self, record: EvaluationRecord) -> Tuple[bool, List[str]]:
        """
        Validate outputs after evaluation

        Returns:
            (is_consistent, list_of_issues)
        """
        issues = []

        if not record.success:
            return True, issues  # Don't validate failed evaluations

        # Consistency validation
        if self.config.get('enable_consistency_validation', True):
            proposition = record.input_data.get('proposition', '')
            result = record.output_data.get('result', False)

            is_consistent, consistency_issues = self.consistency_validator.validate_proposition_consistency(
                proposition, result, record.input_data
            )

            if not is_consistent:
                issues.extend(consistency_issues)
                record.consistency_check = False
            else:
                record.consistency_check = True

        return len(issues) == 0, issues

    @contextmanager
    def _evaluation_context(self, operation: str, **kwargs):
        """Context manager for evaluation monitoring"""
        evaluation_id = str(uuid.uuid4())
        start_time = time.time()

        # Pre-evaluation validation
        is_valid, validation_issues = self._pre_evaluation_validation(operation, **kwargs)

        if not is_valid:
            # Log validation failure
            record = EvaluationRecord(
                evaluation_id=evaluation_id,
                timestamp=start_time,
                evaluator_type="validation",
                operation=operation,
                input_data=kwargs,
                output_data={},
                success=False,
                error_message=f"Pre-validation failed: {', '.join(validation_issues)}",
                execution_time_ms=0,
                metadata={'validation_issues': validation_issues},
                anomaly_flags=[],
                consistency_check=False
            )
            self._log_evaluation(record)
            raise ProofBridgeError(f"Validation failed: {', '.join(validation_issues)}")

        try:
            yield evaluation_id, start_time
        except Exception as e:
            # Log error
            execution_time = (time.time() - start_time) * 1000
            record = EvaluationRecord(
                evaluation_id=evaluation_id,
                timestamp=start_time,
                evaluator_type="error",
                operation=operation,
                input_data=kwargs,
                output_data={},
                success=False,
                error_message=str(e),
                execution_time_ms=execution_time,
                metadata={},
                anomaly_flags=[],
                consistency_check=False
            )
            self._log_evaluation(record)

            # Update error tracking
            with self.state._lock:
                self.state.error_count += 1
                self.state.error_patterns[type(e).__name__] += 1

            raise

    def evaluate_modal_proposition(self, proposition: str, **kwargs) -> Dict[str, Any]:
        """
        Monitored modal logic proposition evaluation
        """
        with self._evaluation_context('evaluate_modal_proposition',
                                     proposition=proposition, **kwargs) as (eval_id, start_time):

            # Perform evaluation
            result = self.modal_evaluator.evaluate_modal_proposition(proposition, **kwargs)
            execution_time = (time.time() - start_time) * 1000

            # Create evaluation record
            record = EvaluationRecord(
                evaluation_id=eval_id,
                timestamp=start_time,
                evaluator_type="modal_logic",
                operation="evaluate_modal_proposition",
                input_data={'proposition': proposition, **kwargs},
                output_data=result,
                success=result.get('success', False),
                error_message=result.get('error'),
                execution_time_ms=execution_time,
                metadata={'evaluator': 'ModalLogicEvaluator'},
                anomaly_flags=[],
                consistency_check=True
            )

            # Post-evaluation validation
            is_consistent, consistency_issues = self._post_evaluation_validation(record)
            if not is_consistent:
                record.anomaly_flags.extend(['consistency_violation'])
                logger.warning(f"Consistency violation in {eval_id}: {consistency_issues}")

            # Anomaly detection
            if self.config.get('enable_anomaly_detection', True):
                anomalies = self.anomaly_detector.analyze_evaluation(
                    record, list(self.state.recent_evaluations)
                )
                record.anomaly_flags.extend(anomalies)

            # Update state and log
            with self.state._lock:
                self.state.evaluation_count += 1
                self.state.recent_evaluations.append(record)
                if record.anomaly_flags:
                    self.state.anomaly_count += 1

            self._log_evaluation(record)

            # Check for emergency conditions
            self._check_emergency_conditions()

            return result

    def evaluate_iel_proposition(self, proposition: str, **kwargs) -> Dict[str, Any]:
        """
        Monitored IEL proposition evaluation
        """
        with self._evaluation_context('evaluate_iel_proposition',
                                     proposition=proposition, **kwargs) as (eval_id, start_time):

            # Perform evaluation
            result = self.iel_evaluator.evaluate_iel_proposition(proposition, **kwargs)
            execution_time = (time.time() - start_time) * 1000

            # Create evaluation record
            record = EvaluationRecord(
                evaluation_id=eval_id,
                timestamp=start_time,
                evaluator_type="iel",
                operation="evaluate_iel_proposition",
                input_data={'proposition': proposition, **kwargs},
                output_data=result,
                success=result.get('success', False),
                error_message=result.get('error'),
                execution_time_ms=execution_time,
                metadata={'evaluator': 'IELEvaluator'},
                anomaly_flags=[],
                consistency_check=True
            )

            # Post-evaluation validation and anomaly detection
            is_consistent, consistency_issues = self._post_evaluation_validation(record)
            if not is_consistent:
                record.anomaly_flags.extend(['consistency_violation'])

            if self.config.get('enable_anomaly_detection', True):
                anomalies = self.anomaly_detector.analyze_evaluation(
                    record, list(self.state.recent_evaluations)
                )
                record.anomaly_flags.extend(anomalies)

            # Update state and log
            with self.state._lock:
                self.state.evaluation_count += 1
                self.state.recent_evaluations.append(record)
                if record.anomaly_flags:
                    self.state.anomaly_count += 1

            self._log_evaluation(record)
            self._check_emergency_conditions()

            return result

    def evaluate_batch(self, propositions: List[str], **kwargs) -> Dict[str, Any]:
        """
        Monitored batch evaluation
        """
        batch_results = []
        batch_anomalies = []

        for i, proposition in enumerate(propositions):
            try:
                if 'I(' in proposition or 'E(' in proposition:
                    result = self.evaluate_iel_proposition(proposition, **kwargs)
                else:
                    result = self.evaluate_modal_proposition(proposition, **kwargs)
                batch_results.append(result)
            except Exception as e:
                error_result = {
                    'success': False,
                    'error': str(e),
                    'proposition_index': i
                }
                batch_results.append(error_result)
                batch_anomalies.append(f"Batch item {i} failed: {str(e)}")

        return {
            'batch_results': batch_results,
            'total_count': len(propositions),
            'success_count': sum(1 for r in batch_results if r.get('success', False)),
            'batch_anomalies': batch_anomalies
        }

    def _check_emergency_conditions(self):
        """Check if emergency halt conditions are met"""
        if not self.enable_circuit_breaker:
            return

        with self.state._lock:
            # Check error rate in last minute
            current_time = time.time()
            recent_errors = [
                r for r in self.state.recent_evaluations
                if not r.success and (current_time - r.timestamp) < 60
            ]

            if len(recent_errors) >= self.max_errors_per_minute:
                self.emergency_halt = True
                logger.critical(f"EMERGENCY HALT: {len(recent_errors)} errors in last minute")

    def get_monitor_status(self) -> Dict[str, Any]:
        """Get current monitor status and statistics"""
        with self.state._lock:
            recent_evaluations = list(self.state.recent_evaluations)

        current_time = time.time()
        recent_errors = [r for r in recent_evaluations if not r.success and (current_time - r.timestamp) < 300]
        recent_anomalies = [r for r in recent_evaluations if r.anomaly_flags and (current_time - r.timestamp) < 300]

        return {
            'monitor_status': 'emergency_halt' if self.emergency_halt else 'operational',
            'total_evaluations': self.state.evaluation_count,
            'total_errors': self.state.error_count,
            'total_anomalies': self.state.anomaly_count,
            'recent_errors_5min': len(recent_errors),
            'recent_anomalies_5min': len(recent_anomalies),
            'blocked_operations': list(self.state.blocked_operations),
            'warning_conditions': list(self.state.warning_conditions),
            'error_patterns': dict(self.state.error_patterns),
            'config': self.config
        }

    def clear_emergency_halt(self, authorization_code: str = None):
        """Clear emergency halt state (requires authorization)"""
        # In production, this would require proper authorization
        if authorization_code == "EMERGENCY_OVERRIDE_2025":
            self.emergency_halt = False
            logger.info("Emergency halt cleared by authorization")
        else:
            logger.warning("Unauthorized attempt to clear emergency halt")

    def add_blocked_operation(self, operation: str, reason: str):
        """Block a specific operation"""
        with self.state._lock:
            self.state.blocked_operations.add(operation)
        logger.warning(f"Blocked operation {operation}: {reason}")

    def remove_blocked_operation(self, operation: str):
        """Unblock a specific operation"""
        with self.state._lock:
            self.state.blocked_operations.discard(operation)
        logger.info(f"Unblocked operation {operation}")

# Global monitor instance
_global_monitor = None

def get_global_monitor() -> EnhancedReferenceMonitor:
    """Get or create global monitor instance"""
    global _global_monitor
    if _global_monitor is None:
        _global_monitor = EnhancedReferenceMonitor()
    return _global_monitor

def shutdown_monitor():
    """Shutdown global monitor"""
    global _global_monitor
    if _global_monitor:
        logger.info("Shutting down Enhanced Reference Monitor")
        _global_monitor = None
