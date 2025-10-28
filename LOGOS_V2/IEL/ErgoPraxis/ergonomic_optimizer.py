"""
Ergonomic Optimization Framework

Provides optimization algorithms for ergonomic systems,
balancing efficiency, user experience, and resource constraints.
"""

from typing import Dict, List, Any, Optional, Tuple, Callable
from dataclasses import dataclass
from enum import Enum
import math

class OptimizationGoal(Enum):
    EFFICIENCY = "efficiency"
    USER_EXPERIENCE = "user_experience"
    RESOURCE_CONSERVATION = "resource_conservation"
    RELIABILITY = "reliability"
    ADAPTABILITY = "adaptability"

@dataclass
class ErgonomicConstraint:
    """Represents a constraint in the ergonomic optimization."""
    name: str
    constraint_type: str  # "equality", "inequality", "bound"
    value: float
    tolerance: float = 0.0

@dataclass
class OptimizationVariable:
    """Represents a variable in the optimization problem."""
    name: str
    bounds: Tuple[float, float]
    initial_value: float
    variable_type: str = "continuous"  # "continuous", "integer", "binary"

class ErgonomicOptimizer:
    """
    Optimizer for ergonomic systems.

    Balances multiple objectives including efficiency, user experience,
    resource usage, and system reliability.
    """

    def __init__(self):
        self.variables: Dict[str, OptimizationVariable] = {}
        self.constraints: List[ErgonomicConstraint] = []
        self.objectives: Dict[str, Callable] = {}
        self.optimization_history: List[Dict[str, Any]] = []

    def add_variable(self, variable: OptimizationVariable):
        """Add an optimization variable."""
        self.variables[variable.name] = variable

    def add_constraint(self, constraint: ErgonomicConstraint):
        """Add an optimization constraint."""
        self.constraints.append(constraint)

    def add_objective(self, name: str, objective_function: Callable,
                     weight: float = 1.0, goal: OptimizationGoal = OptimizationGoal.EFFICIENCY):
        """Add an objective function."""
        self.objectives[name] = {
            "function": objective_function,
            "weight": weight,
            "goal": goal
        }

    def optimize(self, method: str = "gradient_descent",
                max_iterations: int = 100) -> Dict[str, Any]:
        """Run optimization using specified method."""
        if method == "gradient_descent":
            return self._gradient_descent_optimization(max_iterations)
        elif method == "simulated_annealing":
            return self._simulated_annealing_optimization(max_iterations)
        else:
            return self._simple_optimization()

    def _simple_optimization(self) -> Dict[str, Any]:
        """Simple optimization for demonstration."""
        # Initialize with current values
        current_values = {name: var.initial_value for name, var in self.variables.items()}

        # Evaluate objectives
        objective_values = {}
        total_score = 0.0

        for obj_name, obj_config in self.objectives.items():
            try:
                value = obj_config["function"](current_values)
                objective_values[obj_name] = value
                total_score += value * obj_config["weight"]
            except Exception as e:
                objective_values[obj_name] = 0.0

        result = {
            "method": "simple",
            "optimal_values": current_values,
            "objective_values": objective_values,
            "total_score": total_score,
            "constraints_satisfied": self._check_constraints(current_values),
            "iterations": 1
        }

        self.optimization_history.append(result)
        return result

    def _gradient_descent_optimization(self, max_iterations: int) -> Dict[str, Any]:
        """Gradient descent optimization."""
        # Simplified gradient descent
        current_values = {name: var.initial_value for name, var in self.variables.items()}
        learning_rate = 0.01

        best_score = float('-inf')
        best_values = current_values.copy()

        for iteration in range(max_iterations):
            # Calculate gradient (simplified)
            gradient = self._calculate_gradient(current_values)

            # Update values
            for var_name in current_values:
                if var_name in gradient:
                    new_value = current_values[var_name] + learning_rate * gradient[var_name]
                    # Apply bounds
                    var_bounds = self.variables[var_name].bounds
                    current_values[var_name] = max(var_bounds[0], min(var_bounds[1], new_value))

            # Evaluate
            score = self._evaluate_total_score(current_values)
            if score > best_score:
                best_score = score
                best_values = current_values.copy()

        return {
            "method": "gradient_descent",
            "optimal_values": best_values,
            "total_score": best_score,
            "constraints_satisfied": self._check_constraints(best_values),
            "iterations": max_iterations
        }

    def _simulated_annealing_optimization(self, max_iterations: int) -> Dict[str, Any]:
        """Simulated annealing optimization."""
        current_values = {name: var.initial_value for name, var in self.variables.items()}
        current_score = self._evaluate_total_score(current_values)

        best_values = current_values.copy()
        best_score = current_score

        temperature = 1.0
        cooling_rate = 0.95

        for iteration in range(max_iterations):
            # Generate neighbor solution
            neighbor_values = self._generate_neighbor(current_values)

            # Evaluate neighbor
            neighbor_score = self._evaluate_total_score(neighbor_values)

            # Accept or reject
            if neighbor_score > current_score or math.exp((neighbor_score - current_score) / temperature) > 0.5:
                current_values = neighbor_values
                current_score = neighbor_score

                if current_score > best_score:
                    best_values = current_values.copy()
                    best_score = current_score

            temperature *= cooling_rate

        return {
            "method": "simulated_annealing",
            "optimal_values": best_values,
            "total_score": best_score,
            "constraints_satisfied": self._check_constraints(best_values),
            "iterations": max_iterations
        }

    def _calculate_gradient(self, values: Dict[str, float]) -> Dict[str, float]:
        """Calculate gradient for gradient descent."""
        gradient = {}
        epsilon = 1e-6

        for var_name in values:
            # Numerical gradient
            values_plus = values.copy()
            values_plus[var_name] += epsilon
            values_minus = values.copy()
            values_minus[var_name] -= epsilon

            grad = (self._evaluate_total_score(values_plus) - self._evaluate_total_score(values_minus)) / (2 * epsilon)
            gradient[var_name] = grad

        return gradient

    def _generate_neighbor(self, values: Dict[str, float]) -> Dict[str, float]:
        """Generate a neighbor solution for simulated annealing."""
        neighbor = values.copy()
        # Random perturbation
        for var_name in neighbor:
            bounds = self.variables[var_name].bounds
            range_size = bounds[1] - bounds[0]
            perturbation = (0.5 - 0.5) * range_size * 0.1  # Small random change
            neighbor[var_name] = max(bounds[0], min(bounds[1], neighbor[var_name] + perturbation))
        return neighbor

    def _evaluate_total_score(self, values: Dict[str, float]) -> float:
        """Evaluate total objective score."""
        total_score = 0.0
        for obj_config in self.objectives.values():
            try:
                value = obj_config["function"](values)
                total_score += value * obj_config["weight"]
            except:
                pass
        return total_score

    def _check_constraints(self, values: Dict[str, float]) -> bool:
        """Check if constraints are satisfied."""
        for constraint in self.constraints:
            if constraint.constraint_type == "bound":
                if constraint.name in values:
                    value = values[constraint.name]
                    if not (constraint.value - constraint.tolerance <= value <= constraint.value + constraint.tolerance):
                        return False
        return True

    def get_optimization_history(self) -> List[Dict[str, Any]]:
        """Get optimization history."""
        return self.optimization_history

    def reset(self):
        """Reset the optimizer."""
        self.variables.clear()
        self.constraints.clear()
        self.objectives.clear()
        self.optimization_history.clear()