# --- START OF FILE core/principles.py ---

#!/usr/bin/env python3
"""
Core Principles for LOGOS AGI
Fundamental principles and constraints that govern system behavior

This module implements the Trinity-grounded principles that ensure all
AGI operations align with existence, goodness, and truth.

File: core/principles.py
Author: LOGOS AGI Development Team
Version: 2.0.0
Date: 2025-01-28
"""

import time
import logging
from typing import Dict, List, Tuple, Any, Optional, Callable
from dataclasses import dataclass
from enum import Enum
from abc import ABC, abstractmethod
from functools import wraps

from core.data_structures import SystemState, ValidationStatus, ProcessingPriority

# =========================================================================
# I. FOUNDATIONAL PRINCIPLES
# =========================================================================


class PrincipleType(Enum):
    """Types of governing principles"""

    ONTOLOGICAL = "ontological"  # Being and existence
    LOGICAL = "logical"  # Reasoning and inference
    MORAL = "moral"  # Good and evil
    EPISTEMIC = "epistemic"  # Knowledge and truth
    OPERATIONAL = "operational"  # System behavior


class PrincipleScope(Enum):
    """Scope of principle application"""

    UNIVERSAL = "universal"  # Applies to all operations
    SUBSYSTEM = "subsystem"  # Applies to specific subsystem
    OPERATION = "operation"  # Applies to specific operation type
    CONTEXT = "context"  # Applies in specific contexts


@dataclass
class PrincipleViolation:
    """Record of principle violation"""

    principle_id: str
    violation_description: str
    severity: str  # minor, major, critical
    timestamp: float
    context: Dict[str, Any]
    remediation_suggested: Optional[str] = None


class Principle(ABC):
    """Abstract base class for all principles"""

    def __init__(
        self,
        principle_id: str,
        name: str,
        description: str,
        principle_type: PrincipleType,
        scope: PrincipleScope,
    ):
        self.principle_id = principle_id
        self.name = name
        self.description = description
        self.principle_type = principle_type
        self.scope = scope
        self.logger = logging.getLogger(f"Principle.{principle_id}")

    @abstractmethod
    def evaluate(self, operation_data: Dict[str, Any]) -> Tuple[bool, Optional[str]]:
        """
        Evaluate if operation complies with this principle

        Returns:
            Tuple[bool, Optional[str]]: (complies, violation_reason)
        """
        pass

    def create_violation(
        self, description: str, severity: str, context: Dict[str, Any]
    ) -> PrincipleViolation:
        """Create violation record"""
        return PrincipleViolation(
            principle_id=self.principle_id,
            violation_description=description,
            severity=severity,
            timestamp=time.time(),
            context=context,
        )


# =========================================================================
# II. TRINITY PRINCIPLES
# =========================================================================


class TrinityExistencePrinciple(Principle):
    """Principle ensuring operations respect existence and being"""

    def __init__(self):
        super().__init__(
            principle_id="trinity_existence",
            name="Trinity Existence Principle",
            description="All operations must be grounded in existence and being",
            principle_type=PrincipleType.ONTOLOGICAL,
            scope=PrincipleScope.UNIVERSAL,
        )

    def evaluate(self, operation_data: Dict[str, Any]) -> Tuple[bool, Optional[str]]:
        """Evaluate existence grounding"""

        # Check if operation involves real entities
        entity = operation_data.get("entity")
        if not entity:
            return False, "Operation lacks entity grounding"

        # Check for anti-existence operations
        operation = operation_data.get("operation", "")
        anti_existence_ops = ["destroy", "annihilate", "void", "nihilate"]

        if any(anti_op in operation.lower() for anti_op in anti_existence_ops):
            return False, f"Operation '{operation}' violates existence principle"

        # Verify positive existence orientation
        existence_keywords = ["create", "build", "establish", "form", "generate"]
        has_positive_existence = any(keyword in operation.lower() for keyword in existence_keywords)

        if not has_positive_existence and operation.lower() in ["harm", "damage", "corrupt"]:
            return False, "Operation lacks positive existence orientation"

        return True, None


class TrinityGoodnessPrinciple(Principle):
    """Principle ensuring operations align with goodness"""

    def __init__(self):
        super().__init__(
            principle_id="trinity_goodness",
            name="Trinity Goodness Principle",
            description="All operations must be oriented toward goodness",
            principle_type=PrincipleType.MORAL,
            scope=PrincipleScope.UNIVERSAL,
        )

    def evaluate(self, operation_data: Dict[str, Any]) -> Tuple[bool, Optional[str]]:
        """Evaluate goodness orientation"""

        operation = operation_data.get("operation", "")
        intent = operation_data.get("intent", "")

        # Check for explicitly evil operations
        evil_operations = [
            "harm",
            "damage",
            "destroy",
            "corrupt",
            "deceive",
            "manipulate",
            "exploit",
            "abuse",
            "torture",
            "kill",
            "steal",
            "lie",
        ]

        operation_lower = operation.lower()
        intent_lower = intent.lower()

        for evil_op in evil_operations:
            if evil_op in operation_lower or evil_op in intent_lower:
                return False, f"Operation contains evil element: {evil_op}"

        # Check for positive goodness indicators
        goodness_indicators = [
            "help",
            "assist",
            "heal",
            "protect",
            "serve",
            "benefit",
            "improve",
            "enhance",
            "support",
            "care",
            "love",
            "create",
        ]

        has_goodness = any(
            indicator in operation_lower or indicator in intent_lower
            for indicator in goodness_indicators
        )

        # Neutral operations are acceptable, but explicit evil is not
        return True, None


class TrinityTruthPrinciple(Principle):
    """Principle ensuring operations respect truth"""

    def __init__(self):
        super().__init__(
            principle_id="trinity_truth",
            name="Trinity Truth Principle",
            description="All operations must be grounded in truth",
            principle_type=PrincipleType.EPISTEMIC,
            scope=PrincipleScope.UNIVERSAL,
        )

    def evaluate(self, operation_data: Dict[str, Any]) -> Tuple[bool, Optional[str]]:
        """Evaluate truth grounding"""

        proposition = operation_data.get("proposition", "")
        operation = operation_data.get("operation", "")

        # Check for explicit falsehood
        if "lie" in operation.lower() or "deceive" in operation.lower():
            return False, "Operation involves deception or falsehood"

        # Check for logical contradictions in proposition
        if proposition:
            prop_lower = proposition.lower()

            # Simple contradiction detection
            if "true" in prop_lower and "false" in prop_lower and "same" in prop_lower:
                return False, "Proposition contains logical contradiction"

            # Check for undefined terms being asserted as true
            undefined_assertions = ["undefined is true", "nothing is everything"]
            if any(assertion in prop_lower for assertion in undefined_assertions):
                return False, "Proposition asserts undefined terms as true"

        # Truth principle satisfied if no explicit falsehood detected
        return True, None


# =========================================================================
# III. LOGICAL PRINCIPLES
# =========================================================================


class NonContradictionPrinciple(Principle):
    """Principle of non-contradiction (¬(P ∧ ¬P))"""

    def __init__(self):
        super().__init__(
            principle_id="non_contradiction",
            name="Non-Contradiction Principle",
            description="Nothing can be both true and false simultaneously",
            principle_type=PrincipleType.LOGICAL,
            scope=PrincipleScope.UNIVERSAL,
        )

    def evaluate(self, operation_data: Dict[str, Any]) -> Tuple[bool, Optional[str]]:
        """Evaluate for logical contradictions"""

        propositions = operation_data.get("propositions", [])
        if not propositions:
            return True, None

        # Simple contradiction detection
        positive_claims = set()
        negative_claims = set()

        for prop in propositions:
            prop_text = str(prop).lower().strip()

            if prop_text.startswith("not ") or " is not " in prop_text:
                negative_claims.add(prop_text.replace("not ", "").replace(" is not ", " is "))
            else:
                positive_claims.add(prop_text)

        # Check for direct contradictions
        contradictions = positive_claims.intersection(negative_claims)
        if contradictions:
            return False, f"Contradictory propositions detected: {contradictions}"

        return True, None


class ExcludedMiddlePrinciple(Principle):
    """Principle of excluded middle (P ∨ ¬P)"""

    def __init__(self):
        super().__init__(
            principle_id="excluded_middle",
            name="Excluded Middle Principle",
            description="Every proposition is either true or false",
            principle_type=PrincipleType.LOGICAL,
            scope=PrincipleScope.UNIVERSAL,
        )

    def evaluate(self, operation_data: Dict[str, Any]) -> Tuple[bool, Optional[str]]:
        """Evaluate excluded middle compliance"""

        proposition = operation_data.get("proposition", "")

        if not proposition:
            return True, None

        prop_lower = proposition.lower()

        # Check for explicit middle-state assertions
        middle_violations = [
            "neither true nor false",
            "both true and false",
            "undefined truth value",
            "partially true",
        ]

        for violation in middle_violations:
            if violation in prop_lower:
                return False, f"Proposition violates excluded middle: {violation}"

        return True, None


# =========================================================================
# IV. OPERATIONAL PRINCIPLES
# =========================================================================


class TrinityOptimalityPrinciple(Principle):
    """Principle that operations should optimize for Trinity (n=3)"""

    def __init__(self):
        super().__init__(
            principle_id="trinity_optimality",
            name="Trinity Optimality Principle",
            description="Operations should be structured for Trinity optimization",
            principle_type=PrincipleType.OPERATIONAL,
            scope=PrincipleScope.UNIVERSAL,
        )

    def evaluate(self, operation_data: Dict[str, Any]) -> Tuple[bool, Optional[str]]:
        """Evaluate Trinity optimization"""

        # Check if operation respects Trinity structure
        structure = operation_data.get("structure", {})

        # Look for Trinity-aligned patterns
        trinity_indicators = [
            len(structure.get("components", [])) == 3,
            "existence" in str(operation_data).lower(),
            "goodness" in str(operation_data).lower(),
            "truth" in str(operation_data).lower(),
        ]

        # Operation should have some Trinity alignment
        trinity_alignment_score = sum(trinity_indicators) / len(trinity_indicators)

        if trinity_alignment_score < 0.25:  # Less than 25% Trinity alignment
            return False, "Operation lacks Trinity structural alignment"

        return True, None


class CoherencePrinciple(Principle):
    """Principle ensuring operational coherence"""

    def __init__(self):
        super().__init__(
            principle_id="coherence",
            name="Coherence Principle",
            description="Operations must be internally coherent",
            principle_type=PrincipleType.OPERATIONAL,
            scope=PrincipleScope.UNIVERSAL,
        )

    def evaluate(self, operation_data: Dict[str, Any]) -> Tuple[bool, Optional[str]]:
        """Evaluate operational coherence"""

        # Check for required fields
        required_fields = ["operation", "entity"]
        missing_fields = [field for field in required_fields if field not in operation_data]

        if missing_fields:
            return False, f"Operation lacks coherent structure: missing {missing_fields}"

        # Check for self-referential paradoxes
        operation = operation_data.get("operation", "")
        entity = operation_data.get("entity", "")

        if operation == "self-reference" and entity == "self":
            return False, "Self-referential paradox detected"

        return True, None


# =========================================================================
# V. PRINCIPLE ENGINE
# =========================================================================


class PrincipleEngine:
    """Central engine for principle evaluation and enforcement"""

    def __init__(self):
        self.principles: Dict[str, Principle] = {}
        self.violations: List[PrincipleViolation] = []
        self.logger = logging.getLogger("PrincipleEngine")

        # Register core Trinity principles
        self.register_principle(TrinityExistencePrinciple())
        self.register_principle(TrinityGoodnessPrinciple())
        self.register_principle(TrinityTruthPrinciple())

        # Register logical principles
        self.register_principle(NonContradictionPrinciple())
        self.register_principle(ExcludedMiddlePrinciple())

        # Register operational principles
        self.register_principle(TrinityOptimalityPrinciple())
        self.register_principle(CoherencePrinciple())

    def register_principle(self, principle: Principle):
        """Register a new principle"""
        self.principles[principle.principle_id] = principle
        self.logger.info(f"Registered principle: {principle.name}")

    def evaluate_operation(self, operation_data: Dict[str, Any]) -> Dict[str, Any]:
        """Evaluate operation against all applicable principles"""

        results = {}
        violations = []
        all_compliant = True

        for principle_id, principle in self.principles.items():
            try:
                compliant, violation_reason = principle.evaluate(operation_data)

                results[principle_id] = {
                    "compliant": compliant,
                    "principle_name": principle.name,
                    "violation_reason": violation_reason,
                }

                if not compliant:
                    all_compliant = False
                    violation = principle.create_violation(
                        violation_reason or "Principle violation", "major", operation_data
                    )
                    violations.append(violation)
                    self.violations.append(violation)

            except Exception as e:
                self.logger.error(f"Error evaluating principle {principle_id}: {e}")
                results[principle_id] = {
                    "compliant": False,
                    "principle_name": principle.name,
                    "violation_reason": f"Evaluation error: {e}",
                }
                all_compliant = False

        return {
            "overall_compliant": all_compliant,
            "principle_results": results,
            "violations": [v.__dict__ for v in violations],
            "evaluation_timestamp": time.time(),
        }

    def get_violations(self, severity: Optional[str] = None) -> List[PrincipleViolation]:
        """Get violations, optionally filtered by severity"""
        if severity:
            return [v for v in self.violations if v.severity == severity]
        return self.violations.copy()

    def clear_violations(self):
        """Clear violation history"""
        self.violations.clear()


# =========================================================================
# VI. DECORATORS FOR PRINCIPLE ENFORCEMENT
# =========================================================================


def validate_with_principles(engine: PrincipleEngine):
    """Decorator to validate function calls with principles"""

    def decorator(func: Callable):
        @wraps(func)
        def wrapper(*args, **kwargs):
            # Extract operation data from function call
            operation_data = {
                "operation": func.__name__,
                "entity": kwargs.get("entity", "unknown"),
                "proposition": kwargs.get("proposition", ""),
                "context": kwargs,
            }

            # Evaluate principles
            evaluation = engine.evaluate_operation(operation_data)

            if not evaluation["overall_compliant"]:
                raise ValueError(f"Operation violates principles: {evaluation['violations']}")

            # Execute original function
            return func(*args, **kwargs)

        return wrapper

    return decorator


def require_trinity_grounding(func: Callable):
    """Decorator requiring Trinity grounding for operations"""

    @wraps(func)
    def wrapper(*args, **kwargs):
        # Check for Trinity grounding
        has_existence = "entity" in kwargs
        has_goodness = kwargs.get("intent", "").lower() not in ["harm", "destroy"]
        has_truth = "proposition" in kwargs or kwargs.get("truthful", True)

        if not (has_existence and has_goodness and has_truth):
            raise ValueError("Operation lacks Trinity grounding (existence, goodness, truth)")

        return func(*args, **kwargs)

    return wrapper


# =========================================================================
# VII. MODULE EXPORTS
# =========================================================================

__all__ = [
    # Enums
    "PrincipleType",
    "PrincipleScope",
    # Base classes
    "Principle",
    "PrincipleViolation",
    # Trinity principles
    "TrinityExistencePrinciple",
    "TrinityGoodnessPrinciple",
    "TrinityTruthPrinciple",
    # Logical principles
    "NonContradictionPrinciple",
    "ExcludedMiddlePrinciple",
    # Operational principles
    "TrinityOptimalityPrinciple",
    "CoherencePrinciple",
    # Engine
    "PrincipleEngine",
    # Decorators
    "validate_with_principles",
    "require_trinity_grounding",
]

# --- END OF FILE core/principles.py ---
