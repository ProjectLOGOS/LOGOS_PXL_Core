"""
Resource Management Framework

Provides advanced resource allocation, budgeting, and optimization
capabilities for ergonomic systems.
"""

from typing import Dict, List, Any, Optional, Tuple
from collections import defaultdict
import math

class ResourceManager:
    """
    Advanced resource management system.

    Handles resource allocation, budgeting, regeneration, and optimization
    across multiple domains and time horizons.
    """

    def __init__(self):
        self.resources: Dict[str, Dict[str, Any]] = {}
        self.budgets: Dict[str, Dict[str, Any]] = {}
        self.allocation_history: List[Dict[str, Any]] = []
        self.optimization_goals: Dict[str, Callable] = {}

    def add_resource(self, name: str, initial_quantity: float,
                    max_quantity: float, regeneration_rate: float = 0.0,
                    resource_type: str = "continuous"):
        """Add a resource to the system."""
        self.resources[name] = {
            "quantity": initial_quantity,
            "max_quantity": max_quantity,
            "regeneration_rate": regeneration_rate,
            "type": resource_type,
            "allocations": defaultdict(float),
            "history": []
        }

    def set_budget(self, resource_name: str, period: str, amount: float,
                  reset_interval: Optional[float] = None):
        """Set a budget for a resource over a time period."""
        if resource_name not in self.resources:
            raise ValueError(f"Resource {resource_name} not found")

        self.budgets[f"{resource_name}_{period}"] = {
            "resource": resource_name,
            "period": period,
            "amount": amount,
            "used": 0.0,
            "reset_interval": reset_interval,
            "last_reset": 0.0
        }

    def allocate_resource(self, resource_name: str, amount: float,
                         requester: str, purpose: str = "") -> bool:
        """Allocate resource amount to a requester."""
        if resource_name not in self.resources:
            return False

        resource = self.resources[resource_name]
        if resource["quantity"] < amount:
            return False

        # Check budgets
        for budget_key, budget in self.budgets.items():
            if budget["resource"] == resource_name:
                if budget["used"] + amount > budget["amount"]:
                    return False

        # Allocate
        resource["quantity"] -= amount
        resource["allocations"][requester] += amount

        # Update budgets
        for budget_key, budget in self.budgets.items():
            if budget["resource"] == resource_name:
                budget["used"] += amount

        # Record allocation
        allocation_record = {
            "resource": resource_name,
            "amount": amount,
            "requester": requester,
            "purpose": purpose,
            "timestamp": 0.0  # Would use actual timestamp
        }
        self.allocation_history.append(allocation_record)
        resource["history"].append(allocation_record)

        return True

    def deallocate_resource(self, resource_name: str, amount: float,
                          requester: str) -> bool:
        """Deallocate resource from a requester."""
        if resource_name not in self.resources:
            return False

        resource = self.resources[resource_name]
        if resource["allocations"][requester] < amount:
            return False

        resource["quantity"] += amount
        resource["allocations"][requester] -= amount

        return True

    def regenerate_resources(self, time_delta: float):
        """Regenerate resources over time."""
        for resource in self.resources.values():
            if resource["regeneration_rate"] > 0:
                old_quantity = resource["quantity"]
                resource["quantity"] = min(
                    resource["max_quantity"],
                    resource["quantity"] + resource["regeneration_rate"] * time_delta
                )

    def optimize_allocation(self, requirements: Dict[str, float],
                          constraints: Dict[str, Any] = None) -> Dict[str, float]:
        """Optimize resource allocation given requirements."""
        # Simplified linear programming approach
        allocation = {}

        # Check if requirements can be met
        total_required = sum(requirements.values())
        total_available = sum(r["quantity"] for r in self.resources.values())

        if total_required > total_available:
            # Scale down requirements proportionally
            scale_factor = total_available / total_required
            requirements = {k: v * scale_factor for k, v in requirements.items()}

        # Simple proportional allocation
        for resource_name, required in requirements.items():
            if resource_name in self.resources:
                available = self.resources[resource_name]["quantity"]
                allocation[resource_name] = min(required, available)

        return allocation

    def get_resource_utilization(self) -> Dict[str, Dict[str, Any]]:
        """Get resource utilization statistics."""
        utilization = {}
        for name, resource in self.resources.items():
            utilization[name] = {
                "current_quantity": resource["quantity"],
                "max_quantity": resource["max_quantity"],
                "utilization_ratio": resource["quantity"] / resource["max_quantity"],
                "active_allocations": dict(resource["allocations"]),
                "total_allocated": sum(resource["allocations"].values())
            }
        return utilization

    def get_budget_status(self) -> Dict[str, Dict[str, Any]]:
        """Get budget status for all resources."""
        status = {}
        for budget_key, budget in self.budgets.items():
            status[budget_key] = {
                "resource": budget["resource"],
                "period": budget["period"],
                "budget_amount": budget["amount"],
                "used_amount": budget["used"],
                "remaining": budget["amount"] - budget["used"],
                "utilization_ratio": budget["used"] / budget["amount"] if budget["amount"] > 0 else 0
            }
        return status

    def forecast_resource_needs(self, time_horizon: float,
                              consumption_rate: Dict[str, float]) -> Dict[str, Any]:
        """Forecast future resource needs."""
        forecast = {}

        for resource_name, rate in consumption_rate.items():
            if resource_name in self.resources:
                resource = self.resources[resource_name]
                projected_consumption = rate * time_horizon
                projected_quantity = resource["quantity"] - projected_consumption
                regeneration = resource["regeneration_rate"] * time_horizon
                final_quantity = projected_quantity + regeneration

                forecast[resource_name] = {
                    "current_quantity": resource["quantity"],
                    "projected_consumption": projected_consumption,
                    "projected_regeneration": regeneration,
                    "final_quantity": final_quantity,
                    "will_be_depleted": final_quantity <= 0
                }

        return forecast