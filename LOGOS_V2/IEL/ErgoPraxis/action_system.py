"""
Action Systems Framework

Provides classes for modeling actions, their costs, effects,
and optimization under resource constraints.
"""

from typing import Dict, List, Any, Optional, Set, Callable
from dataclasses import dataclass
from enum import Enum
import time

class ActionStatus(Enum):
    PENDING = "pending"
    EXECUTING = "executing"
    COMPLETED = "completed"
    FAILED = "failed"
    CANCELLED = "cancelled"

@dataclass
class Resource:
    """Represents a resource with quantity and constraints."""
    name: str
    quantity: float
    max_quantity: float
    regeneration_rate: float = 0.0

    def consume(self, amount: float) -> bool:
        """Consume resource amount. Returns True if successful."""
        if self.quantity >= amount:
            self.quantity -= amount
            return True
        return False

    def regenerate(self, time_delta: float):
        """Regenerate resource over time."""
        self.quantity = min(self.max_quantity,
                          self.quantity + self.regeneration_rate * time_delta)

@dataclass
class Action:
    """Represents an executable action."""
    name: str
    description: str
    resource_costs: Dict[str, float]
    execution_time: float
    success_probability: float = 1.0
    prerequisites: Set[str] = None
    effects: Dict[str, Any] = None

    def __post_init__(self):
        if self.prerequisites is None:
            self.prerequisites = set()
        if self.effects is None:
            self.effects = {}

class ActionSystem:
    """
    System for managing and executing actions under resource constraints.

    Supports action planning, resource management, and ergonomic optimization.
    """

    def __init__(self):
        self.resources: Dict[str, Resource] = {}
        self.actions: Dict[str, Action] = {}
        self.action_history: List[Dict[str, Any]] = []
        self.current_actions: Dict[str, Dict[str, Any]] = {}

    def add_resource(self, resource: Resource):
        """Add a resource to the system."""
        self.resources[resource.name] = resource

    def add_action(self, action: Action):
        """Add an action to the system."""
        self.actions[action.name] = action

    def check_prerequisites(self, action_name: str) -> bool:
        """Check if action prerequisites are met."""
        if action_name not in self.actions:
            return False

        action = self.actions[action_name]
        for prereq in action.prerequisites:
            if prereq not in self.action_history:
                return False
        return True

    def check_resources(self, action_name: str) -> bool:
        """Check if sufficient resources are available."""
        if action_name not in self.actions:
            return False

        action = self.actions[action_name]
        for resource_name, cost in action.resource_costs.items():
            if resource_name not in self.resources:
                return False
            if self.resources[resource_name].quantity < cost:
                return False
        return True

    def execute_action(self, action_name: str) -> Dict[str, Any]:
        """Execute an action if possible."""
        if action_name not in self.actions:
            return {"status": "error", "message": "Action not found"}

        if not self.check_prerequisites(action_name):
            return {"status": "error", "message": "Prerequisites not met"}

        if not self.check_resources(action_name):
            return {"status": "error", "message": "Insufficient resources"}

        action = self.actions[action_name]

        # Consume resources
        for resource_name, cost in action.resource_costs.items():
            self.resources[resource_name].consume(cost)

        # Start execution
        execution_id = f"{action_name}_{int(time.time())}"
        self.current_actions[execution_id] = {
            "action": action,
            "start_time": time.time(),
            "status": ActionStatus.EXECUTING
        }

        # Simulate execution (in practice would be async)
        time.sleep(action.execution_time)

        # Complete action
        success = True  # Simplified - in practice would check success_probability

        result = {
            "execution_id": execution_id,
            "action": action_name,
            "status": "completed" if success else "failed",
            "resources_consumed": action.resource_costs,
            "execution_time": action.execution_time
        }

        self.action_history.append(result)
        del self.current_actions[execution_id]

        return result

    def get_resource_status(self) -> Dict[str, Dict[str, Any]]:
        """Get current resource status."""
        return {
            name: {
                "quantity": resource.quantity,
                "max_quantity": resource.max_quantity,
                "utilization": resource.quantity / resource.max_quantity
            }
            for name, resource in self.resources.items()
        }

    def get_action_history(self, limit: int = 10) -> List[Dict[str, Any]]:
        """Get recent action history."""
        return self.action_history[-limit:] if limit > 0 else self.action_history

    def optimize_resource_allocation(self, target_actions: List[str]) -> Dict[str, Any]:
        """Optimize resource allocation for target actions."""
        # Simplified optimization - in practice would use linear programming
        total_costs = {}
        for action_name in target_actions:
            if action_name in self.actions:
                for resource, cost in self.actions[action_name].resource_costs.items():
                    total_costs[resource] = total_costs.get(resource, 0) + cost

        return {
            "target_actions": target_actions,
            "total_resource_costs": total_costs,
            "feasible": all(
                total_costs.get(resource, 0) <= self.resources[resource].quantity
                for resource in self.resources
            )
        }