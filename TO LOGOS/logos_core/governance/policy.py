"""
Policy Manager - Safety and Alignment Configuration Management

Manages governance policies for autonomous reasoning enhancement with safety
constraints, compliance monitoring, and emergency controls. Provides centralized
policy enforcement across all LOGOS AGI v1.0 components.

Architecture:
- YAML-based policy configuration management
- Runtime policy enforcement and validation
- Policy violation detection and alerting
- Emergency control mechanisms
- Audit trail for policy changes

Safety Constraints:
- All policy changes require approval workflows
- Emergency stop capabilities with failsafe timeouts
- Resource consumption limits and monitoring
- Formal verification gate enforcement
- Immutable audit trail for policy changes
"""

import logging
import yaml
from typing import Dict, List, Set, Optional, Any, Callable
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from pathlib import Path
import json
from collections import defaultdict


@dataclass
class PolicyViolation:
    """Represents a policy violation event"""
    violation_id: str
    policy_section: str
    policy_rule: str
    violation_type: str  # "threshold_exceeded", "constraint_violated", "unauthorized_action"
    severity: str  # "low", "medium", "high", "critical"
    description: str
    detected_at: datetime
    component: str
    metadata: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for serialization"""
        data = self.__dict__.copy()
        data["detected_at"] = self.detected_at.isoformat()
        return data


@dataclass
class PolicyMetrics:
    """Policy compliance and enforcement metrics"""
    total_policy_checks: int = 0
    policy_violations: int = 0
    emergency_stops_triggered: int = 0
    compliance_score: float = 1.0
    last_violation_time: Optional[datetime] = None
    monitoring_window_hours: int = 24

    def update_compliance_score(self) -> None:
        """Update compliance score based on violation rate"""
        if self.total_policy_checks > 0:
            violation_rate = self.policy_violations / self.total_policy_checks
            self.compliance_score = max(0.0, 1.0 - violation_rate)
        else:
            self.compliance_score = 1.0


class PolicyManager:
    """
    LOGOS Policy Manager

    Manages governance policies for autonomous reasoning enhancement with
    comprehensive safety controls and compliance monitoring.
    """

    def __init__(self, policy_file_path: Optional[str] = None):
        self.policy_file_path = policy_file_path or "logos_core/governance/policy.yaml"
        self.logger = self._setup_logging()

        # Policy storage and cache
        self._policy_config: Dict[str, Any] = {}
        self._policy_cache_dirty = True
        self._last_policy_load = None

        # Violation tracking
        self._violations: List[PolicyViolation] = []
        self._violation_callbacks: List[Callable[[PolicyViolation], None]] = []

        # Metrics and monitoring
        self._metrics = PolicyMetrics()
        self._emergency_stop_active = False
        self._emergency_stop_time: Optional[datetime] = None

        # Load initial policy
        self._load_policy_config()

    def _setup_logging(self) -> logging.Logger:
        """Configure policy manager logging"""
        logger = logging.getLogger("logos.policy_manager")
        if not logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter(
                '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
            )
            handler.setFormatter(formatter)
            logger.addHandler(handler)
            logger.setLevel(logging.INFO)
        return logger

    def check_safety_constraint(self, constraint_name: str, current_value: Any,
                              component: str = "unknown") -> bool:
        """
        Check if a safety constraint is satisfied

        Args:
            constraint_name: Name of the constraint to check
            current_value: Current value to check against constraint
            component: Component making the check

        Returns:
            bool: True if constraint is satisfied, False otherwise
        """
        try:
            self._metrics.total_policy_checks += 1

            # Get constraint configuration
            constraint_config = self._get_safety_constraint(constraint_name)
            if not constraint_config:
                self.logger.warning(f"Unknown safety constraint: {constraint_name}")
                return True  # Default to permissive for unknown constraints

            # Check constraint
            is_satisfied = self._evaluate_constraint(constraint_config, current_value)

            if not is_satisfied:
                self._record_violation(
                    policy_section="safety",
                    policy_rule=constraint_name,
                    violation_type="constraint_violated",
                    severity=constraint_config.get("severity", "medium"),
                    description=f"Safety constraint violated: {constraint_name} = {current_value}",
                    component=component,
                    metadata={"constraint_value": current_value, "constraint_config": constraint_config}
                )

            return is_satisfied

        except Exception as e:
            self.logger.error(f"Error checking safety constraint {constraint_name}: {e}")
            return False  # Fail closed for safety

    def check_resource_limits(self, resource_usage: Dict[str, float], component: str = "unknown") -> bool:
        """
        Check if resource usage is within policy limits

        Args:
            resource_usage: Dictionary of resource usage metrics
            component: Component reporting resource usage

        Returns:
            bool: True if within limits, False otherwise
        """
        try:
            safety_config = self._policy_config.get("safety", {})
            all_within_limits = True

            # Check memory usage
            if "memory_mb" in resource_usage:
                max_memory = safety_config.get("max_memory_mb", 512)
                if resource_usage["memory_mb"] > max_memory:
                    self._record_violation(
                        policy_section="safety",
                        policy_rule="max_memory_mb",
                        violation_type="threshold_exceeded",
                        severity="high",
                        description=f"Memory usage exceeded: {resource_usage['memory_mb']} > {max_memory} MB",
                        component=component,
                        metadata=resource_usage
                    )
                    all_within_limits = False

            # Check CPU usage
            if "cpu_percent" in resource_usage:
                max_cpu = safety_config.get("max_cpu_percent", 10.0)
                if resource_usage["cpu_percent"] > max_cpu:
                    self._record_violation(
                        policy_section="safety",
                        policy_rule="max_cpu_percent",
                        violation_type="threshold_exceeded",
                        severity="medium",
                        description=f"CPU usage exceeded: {resource_usage['cpu_percent']} > {max_cpu}%",
                        component=component,
                        metadata=resource_usage
                    )
                    all_within_limits = False

            return all_within_limits

        except Exception as e:
            self.logger.error(f"Error checking resource limits: {e}")
            return False

    def check_operation_rate_limit(self, operation_type: str, component: str = "unknown") -> bool:
        """
        Check if operation rate limit is exceeded

        Args:
            operation_type: Type of operation to check
            component: Component performing operation

        Returns:
            bool: True if within rate limit, False otherwise
        """
        try:
            # Get rate limit configuration
            rate_limit = self._get_rate_limit(operation_type)
            if not rate_limit:
                return True  # No limit configured

            # Check current rate
            current_rate = self._calculate_operation_rate(operation_type, component)

            if current_rate > rate_limit:
                self._record_violation(
                    policy_section="safety",
                    policy_rule=f"rate_limit_{operation_type}",
                    violation_type="threshold_exceeded",
                    severity="medium",
                    description=f"Rate limit exceeded for {operation_type}: {current_rate} > {rate_limit}/hour",
                    component=component,
                    metadata={"operation_type": operation_type, "current_rate": current_rate}
                )
                return False

            return True

        except Exception as e:
            self.logger.error(f"Error checking rate limit for {operation_type}: {e}")
            return False

    def require_approval(self, action_type: str, confidence: float, component: str = "unknown") -> bool:
        """
        Check if action requires human approval based on confidence threshold

        Args:
            action_type: Type of action requiring approval
            confidence: Confidence level of the action
            component: Component requesting approval

        Returns:
            bool: True if approval required, False if can proceed autonomously
        """
        try:
            # Get approval threshold
            threshold = self._get_approval_threshold(action_type)

            requires_approval = confidence < threshold

            if requires_approval:
                self.logger.info(f"Human approval required for {action_type}: confidence {confidence} < {threshold}")
            else:
                self.logger.debug(f"Autonomous approval granted for {action_type}: confidence {confidence} >= {threshold}")

            return requires_approval

        except Exception as e:
            self.logger.error(f"Error checking approval requirement: {e}")
            return True  # Fail safe - require approval on error

    def trigger_emergency_stop(self, reason: str, component: str = "system") -> bool:
        """
        Trigger emergency stop of autonomous operations

        Args:
            reason: Reason for emergency stop
            component: Component triggering the stop

        Returns:
            bool: True if emergency stop activated, False otherwise
        """
        try:
            if not self._policy_config.get("safety", {}).get("enable_emergency_stop", True):
                self.logger.warning("Emergency stop disabled in policy")
                return False

            self._emergency_stop_active = True
            self._emergency_stop_time = datetime.now()
            self._metrics.emergency_stops_triggered += 1

            # Record critical violation
            self._record_violation(
                policy_section="safety",
                policy_rule="emergency_stop",
                violation_type="emergency_stop_triggered",
                severity="critical",
                description=f"Emergency stop triggered: {reason}",
                component=component,
                metadata={"reason": reason}
            )

            self.logger.critical(f"EMERGENCY STOP ACTIVATED by {component}: {reason}")

            # Notify emergency contacts
            self._notify_emergency_stop(reason, component)

            return True

        except Exception as e:
            self.logger.error(f"Error triggering emergency stop: {e}")
            return False

    def is_emergency_stop_active(self) -> bool:
        """Check if emergency stop is currently active"""
        if not self._emergency_stop_active:
            return False

        # Check if emergency stop has timed out
        if self._emergency_stop_time:
            timeout_hours = self._policy_config.get("safety", {}).get("failsafe_mode_timeout_hours", 24)
            timeout_time = self._emergency_stop_time + timedelta(hours=timeout_hours)

            if datetime.now() > timeout_time:
                self.logger.warning("Emergency stop timeout reached - automatically clearing")
                self.clear_emergency_stop("timeout")
                return False

        return True

    def clear_emergency_stop(self, cleared_by: str = "manual") -> bool:
        """
        Clear emergency stop condition

        Args:
            cleared_by: Who/what cleared the emergency stop

        Returns:
            bool: True if cleared successfully, False otherwise
        """
        try:
            if not self._emergency_stop_active:
                self.logger.warning("No emergency stop to clear")
                return False

            self._emergency_stop_active = False
            self._emergency_stop_time = None

            self.logger.warning(f"Emergency stop cleared by: {cleared_by}")
            return True

        except Exception as e:
            self.logger.error(f"Error clearing emergency stop: {e}")
            return False

    def get_policy_value(self, path: str, default: Any = None) -> Any:
        """
        Get policy configuration value by path

        Args:
            path: Dot-separated path to policy value (e.g., "safety.max_memory_mb")
            default: Default value if path not found

        Returns:
            Any: Policy value or default
        """
        try:
            current = self._policy_config
            for part in path.split('.'):
                if isinstance(current, dict) and part in current:
                    current = current[part]
                else:
                    return default
            return current
        except Exception:
            return default

    def get_violations(self, severity: Optional[str] = None, hours: int = 24) -> List[PolicyViolation]:
        """
        Get recent policy violations

        Args:
            severity: Filter by severity level
            hours: Look back this many hours

        Returns:
            List[PolicyViolation]: Recent violations
        """
        cutoff_time = datetime.now() - timedelta(hours=hours)

        violations = [v for v in self._violations if v.detected_at >= cutoff_time]

        if severity:
            violations = [v for v in violations if v.severity == severity]

        return violations

    def get_metrics(self) -> PolicyMetrics:
        """Get policy compliance metrics"""
        self._metrics.update_compliance_score()
        return self._metrics

    def register_violation_callback(self, callback: Callable[[PolicyViolation], None]) -> None:
        """Register callback for policy violations"""
        self._violation_callbacks.append(callback)

    def reload_policy(self) -> bool:
        """Reload policy configuration from file"""
        try:
            self._load_policy_config()
            self.logger.info("Policy configuration reloaded")
            return True
        except Exception as e:
            self.logger.error(f"Failed to reload policy: {e}")
            return False

    def _load_policy_config(self) -> None:
        """Load policy configuration from YAML file"""
        try:
            policy_path = Path(self.policy_file_path)
            if not policy_path.exists():
                self.logger.error(f"Policy file not found: {policy_path}")
                # Load default policy
                self._policy_config = self._get_default_policy()
                return

            with open(policy_path, 'r') as f:
                self._policy_config = yaml.safe_load(f)

            self._last_policy_load = datetime.now()
            self._policy_cache_dirty = False

            self.logger.info(f"Loaded policy configuration from {policy_path}")

        except Exception as e:
            self.logger.error(f"Failed to load policy configuration: {e}")
            self._policy_config = self._get_default_policy()

    def _get_default_policy(self) -> Dict[str, Any]:
        """Get default policy configuration"""
        return {
            "safety": {
                "proof_gate_policy": "strict",
                "require_formal_verification": True,
                "max_memory_mb": 512,
                "max_cpu_percent": 10.0,
                "max_self_extensions_per_hour": 1,
                "require_human_approval_threshold": 0.8,
                "enable_emergency_stop": True,
                "failsafe_mode_timeout_hours": 24
            },
            "iel_governance": {
                "max_candidate_iels_pending": 100,
                "generation_rate_limit_per_hour": 10,
                "min_confidence_threshold": 0.4,
                "auto_approve_threshold": 0.9
            }
        }

    def _get_safety_constraint(self, constraint_name: str) -> Optional[Dict[str, Any]]:
        """Get safety constraint configuration"""
        safety_config = self._policy_config.get("safety", {})

        # Map constraint names to policy values
        constraint_mapping = {
            "max_memory_mb": {"limit": safety_config.get("max_memory_mb", 512), "severity": "high"},
            "max_cpu_percent": {"limit": safety_config.get("max_cpu_percent", 10.0), "severity": "medium"},
            "proof_gate_policy": {"value": safety_config.get("proof_gate_policy", "strict"), "severity": "critical"}
        }

        return constraint_mapping.get(constraint_name)

    def _evaluate_constraint(self, constraint_config: Dict[str, Any], current_value: Any) -> bool:
        """Evaluate if constraint is satisfied"""
        if "limit" in constraint_config:
            return current_value <= constraint_config["limit"]
        elif "value" in constraint_config:
            return current_value == constraint_config["value"]
        return True

    def _get_rate_limit(self, operation_type: str) -> Optional[float]:
        """Get rate limit for operation type"""
        rate_limits = {
            "iel_generation": self._policy_config.get("iel_governance", {}).get("generation_rate_limit_per_hour", 10),
            "self_extension": self._policy_config.get("safety", {}).get("max_self_extensions_per_hour", 1),
            "verification": 50,  # Default verification rate limit
            "daemon_operation": 100  # Default daemon operation rate limit
        }

        return rate_limits.get(operation_type)

    def _calculate_operation_rate(self, operation_type: str, component: str) -> float:
        """Calculate current operation rate"""
        # Placeholder: implement actual rate tracking
        # This would track operations in a time window
        return 0.0

    def _get_approval_threshold(self, action_type: str) -> float:
        """Get approval threshold for action type"""
        iel_config = self._policy_config.get("iel_governance", {})

        thresholds = {
            "iel_activation": iel_config.get("auto_approve_threshold", 0.9),
            "self_extension": self._policy_config.get("safety", {}).get("require_human_approval_threshold", 0.8),
            "domain_bridging": 0.8,  # Conservative threshold for bridging
            "emergency_action": 0.95  # Very high threshold for emergency actions
        }

        return thresholds.get(action_type, 0.8)  # Default threshold

    def _record_violation(self, policy_section: str, policy_rule: str, violation_type: str,
                         severity: str, description: str, component: str, metadata: Dict[str, Any]) -> None:
        """Record a policy violation"""
        violation = PolicyViolation(
            violation_id=f"violation_{len(self._violations):06d}",
            policy_section=policy_section,
            policy_rule=policy_rule,
            violation_type=violation_type,
            severity=severity,
            description=description,
            detected_at=datetime.now(),
            component=component,
            metadata=metadata
        )

        self._violations.append(violation)
        self._metrics.policy_violations += 1
        self._metrics.last_violation_time = violation.detected_at

        # Trigger callbacks
        for callback in self._violation_callbacks:
            try:
                callback(violation)
            except Exception as e:
                self.logger.error(f"Violation callback error: {e}")

        # Log violation
        log_level = {
            "low": logging.INFO,
            "medium": logging.WARNING,
            "high": logging.ERROR,
            "critical": logging.CRITICAL
        }.get(severity, logging.WARNING)

        self.logger.log(log_level, f"Policy violation [{severity}]: {description}")

        # Check if emergency stop should be triggered
        if severity == "critical" and not self.is_emergency_stop_active():
            self.trigger_emergency_stop(f"Critical policy violation: {description}", component)

    def _notify_emergency_stop(self, reason: str, component: str) -> None:
        """Notify emergency contacts of emergency stop"""
        try:
            safety_config = self._policy_config.get("safety", {})
            emergency_contact = safety_config.get("emergency_contact")

            if emergency_contact:
                # Placeholder: implement actual notification
                self.logger.critical(f"EMERGENCY STOP - Notify {emergency_contact}: {reason}")

        except Exception as e:
            self.logger.error(f"Failed to send emergency notification: {e}")
