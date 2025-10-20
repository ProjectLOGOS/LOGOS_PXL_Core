# --- START OF FILE core/lambda_calculus.py ---

#!/usr/bin/env python3
"""
Lambda Calculus Engine for LOGOS AGI
Trinity-grounded lambda calculus with formal computation and reduction

This module implements a complete lambda calculus engine with Trinity-based
evaluation strategies and formal reasoning capabilities.

File: core/lambda_calculus.py
Author: LOGOS AGI Development Team
Version: 2.0.0
Date: 2025-01-28
"""

import time
import logging
import json
from typing import Dict, List, Tuple, Any, Optional, Union, Set
from dataclasses import dataclass, field
from enum import Enum
from abc import ABC, abstractmethod

from core.data_structures import TrinityVector
from core.principles import PrincipleEngine

# =========================================================================
# I. LAMBDA EXPRESSION FOUNDATIONS
# =========================================================================

class ExpressionType(Enum):
    """Types of lambda expressions"""
    VARIABLE = "variable"
    ABSTRACTION = "abstraction"  # λx.M
    APPLICATION = "application"  # M N
    CONSTANT = "constant"
    TRINITY_COMBINATOR = "trinity_combinator"

@dataclass
class LambdaExpression(ABC):
    """Abstract base class for lambda expressions"""
    expression_id: str = field(default_factory=lambda: f"expr_{int(time.time())}_{id(object())}")
    trinity_grounding: TrinityVector = field(default_factory=lambda: TrinityVector(1/3, 1/3, 1/3))
    created_at: float = field(default_factory=time.time)

    @abstractmethod
    def to_string(self) -> str:
        """Convert to string representation"""
        pass

    @abstractmethod
    def free_variables(self) -> Set[str]:
        """Get free variables in expression"""
        pass

    @abstractmethod
    def substitute(self, var: str, replacement: 'LambdaExpression') -> 'LambdaExpression':
        """Substitute variable with replacement expression"""
        pass

    @abstractmethod
    def alpha_equivalent(self, other: 'LambdaExpression') -> bool:
        """Check alpha equivalence with another expression"""
        pass

@dataclass
class Variable(LambdaExpression):
    """Lambda variable"""
    name: str = ""

    def to_string(self) -> str:
        return self.name

    def free_variables(self) -> Set[str]:
        return {self.name}

    def substitute(self, var: str, replacement: LambdaExpression) -> LambdaExpression:
        if self.name == var:
            return replacement
        return self

    def alpha_equivalent(self, other: LambdaExpression) -> bool:
        return isinstance(other, Variable) and self.name == other.name

@dataclass
class Abstraction(LambdaExpression):
    """Lambda abstraction (λx.M)"""
    parameter: str = ""
    body: Optional[LambdaExpression] = None

    def to_string(self) -> str:
        body_str = self.body.to_string() if self.body else "⊥"
        return f"(λ{self.parameter}.{body_str})"

    def free_variables(self) -> Set[str]:
        if self.body:
            return self.body.free_variables() - {self.parameter}
        return set()

    def substitute(self, var: str, replacement: LambdaExpression) -> LambdaExpression:
        if var == self.parameter:
            # Variable is bound, no substitution
            return self

        if self.body:
            # Check for variable capture
            replacement_free_vars = replacement.free_variables()
            if self.parameter in replacement_free_vars:
                # Need α-conversion to avoid capture
                new_param = self._generate_fresh_variable(replacement_free_vars | self.body.free_variables())
                new_body = self.body.substitute(self.parameter, Variable(new_param))
                return Abstraction(
                    parameter=new_param,
                    body=new_body.substitute(var, replacement)
                )
            else:
                return Abstraction(
                    parameter=self.parameter,
                    body=self.body.substitute(var, replacement)
                )

        return self

    def _generate_fresh_variable(self, avoid: Set[str]) -> str:
        """Generate fresh variable name avoiding conflicts"""
        base = self.parameter
        counter = 0
        while True:
            candidate = f"{base}_{counter}" if counter > 0 else f"{base}'"
            if candidate not in avoid:
                return candidate
            counter += 1

    def alpha_equivalent(self, other: LambdaExpression) -> bool:
        if not isinstance(other, Abstraction):
            return False

        if self.body is None or other.body is None:
            return self.body == other.body

        # α-equivalence: rename bound variables to fresh names and compare
        fresh_var = self._generate_fresh_variable(
            self.free_variables() | other.free_variables()
        )

        self_renamed = self.body.substitute(self.parameter, Variable(fresh_var))
        other_renamed = other.body.substitute(other.parameter, Variable(fresh_var))

        return self_renamed.alpha_equivalent(other_renamed)

@dataclass
class Application(LambdaExpression):
    """Lambda application (M N)"""
    function: Optional[LambdaExpression] = None
    argument: Optional[LambdaExpression] = None

    def to_string(self) -> str:
        func_str = self.function.to_string() if self.function else "⊥"
        arg_str = self.argument.to_string() if self.argument else "⊥"
        return f"({func_str} {arg_str})"

    def free_variables(self) -> Set[str]:
        free_vars = set()
        if self.function:
            free_vars.update(self.function.free_variables())
        if self.argument:
            free_vars.update(self.argument.free_variables())
        return free_vars

    def substitute(self, var: str, replacement: LambdaExpression) -> LambdaExpression:
        new_function = self.function.substitute(var, replacement) if self.function else None
        new_argument = self.argument.substitute(var, replacement) if self.argument else None

        return Application(
            function=new_function,
            argument=new_argument
        )

    def alpha_equivalent(self, other: LambdaExpression) -> bool:
        if not isinstance(other, Application):
            return False

        func_equiv = (
            (self.function is None and other.function is None) or
            (self.function is not None and other.function is not None and
             self.function.alpha_equivalent(other.function))
        )

        arg_equiv = (
            (self.argument is None and other.argument is None) or
            (self.argument is not None and other.argument is not None and
             self.argument.alpha_equivalent(other.argument))
        )

        return func_equiv and arg_equiv

@dataclass
class Constant(LambdaExpression):
    """Lambda constant value"""
    value: Any = None
    value_type: str = "unknown"

    def to_string(self) -> str:
        return str(self.value)

    def free_variables(self) -> Set[str]:
        return set()

    def substitute(self, var: str, replacement: LambdaExpression) -> LambdaExpression:
        return self  # Constants don't contain variables

    def alpha_equivalent(self, other: LambdaExpression) -> bool:
        return isinstance(other, Constant) and self.value == other.value

# =========================================================================
# II. TRINITY COMBINATORS
# =========================================================================

class TrinityCombinator(LambdaExpression):
    """Special combinators based on Trinity structure"""

    def __init__(self, combinator_type: str):
        super().__init__()
        self.combinator_type = combinator_type
        self._setup_combinator()

    def _setup_combinator(self):
        """Setup combinator based on type"""

        if self.combinator_type == "EXISTENCE":
            # E combinator: λx.x (identity for existence)
            self.trinity_grounding = TrinityVector(1.0, 0.0, 0.0)
            self.implementation = lambda x: x

        elif self.combinator_type == "GOODNESS":
            # G combinator: λf.λx.f(f(x)) (doubling for goodness amplification)
            self.trinity_grounding = TrinityVector(0.0, 1.0, 0.0)
            self.implementation = lambda f: lambda x: f(f(x))

        elif self.combinator_type == "TRUTH":
            # T combinator: λx.λy.x (constant function for truth preservation)
            self.trinity_grounding = TrinityVector(0.0, 0.0, 1.0)
            self.implementation = lambda x: lambda y: x

        elif self.combinator_type == "TRINITY":
            # Trinity combinator: λf.λg.λh.λx.f(g(h(x))) (three-way composition)
            self.trinity_grounding = TrinityVector(1/3, 1/3, 1/3)
            self.implementation = lambda f: lambda g: lambda h: lambda x: f(g(h(x)))

        else:
            raise ValueError(f"Unknown Trinity combinator type: {self.combinator_type}")

    def to_string(self) -> str:
        return f"#{self.combinator_type}"

    def free_variables(self) -> Set[str]:
        return set()  # Combinators have no free variables

    def substitute(self, var: str, replacement: LambdaExpression) -> LambdaExpression:
        return self  # Combinators are closed terms

    def alpha_equivalent(self, other: LambdaExpression) -> bool:
        return (isinstance(other, TrinityCombinator) and
                self.combinator_type == other.combinator_type)

# =========================================================================
# III. REDUCTION STRATEGIES
# =========================================================================

class ReductionStrategy(Enum):
    """Lambda calculus reduction strategies"""
    CALL_BY_NAME = "call_by_name"           # Outermost reduction
    CALL_BY_VALUE = "call_by_value"         # Innermost reduction
    NORMAL_ORDER = "normal_order"           # Leftmost-outermost
    APPLICATIVE_ORDER = "applicative_order" # Leftmost-innermost
    TRINITY_ORDER = "trinity_order"         # Trinity-grounded reduction

@dataclass
class ReductionStep:
    """Single step in lambda reduction"""
    step_number: int
    expression_before: LambdaExpression
    expression_after: LambdaExpression
    reduction_type: str  # β-reduction, α-conversion, etc.
    position: str = ""   # Position in expression tree

    def to_dict(self) -> Dict[str, Any]:
        return {
            "step_number": self.step_number,
            "before": self.expression_before.to_string(),
            "after": self.expression_after.to_string(),
            "reduction_type": self.reduction_type,
            "position": self.position
        }

class LambdaReducer:
    """Lambda calculus reduction engine"""

    def __init__(self, strategy: ReductionStrategy = ReductionStrategy.NORMAL_ORDER):
        self.strategy = strategy
        self.max_steps = 1000  # Prevent infinite loops
        self.logger = logging.getLogger(__name__)

        # Trinity-based evaluation weights
        self.existence_weight = 0.33
        self.goodness_weight = 0.33
        self.truth_weight = 0.34

    def reduce(self, expression: LambdaExpression) -> Tuple[LambdaExpression, List[ReductionStep]]:
        """Reduce lambda expression to normal form"""

        steps = []
        current_expr = expression
        step_count = 0

        while step_count < self.max_steps:
            # Find next reduction
            next_reduction = self._find_next_reduction(current_expr)

            if next_reduction is None:
                # Normal form reached
                break

            reduced_expr, reduction_type = next_reduction

            step = ReductionStep(
                step_number=step_count + 1,
                expression_before=current_expr,
                expression_after=reduced_expr,
                reduction_type=reduction_type
            )

            steps.append(step)
            current_expr = reduced_expr
            step_count += 1

            # Check for loops (simplified)
            if step_count > 10:
                recent_expressions = [s.expression_after.to_string() for s in steps[-5:]]
                if len(set(recent_expressions)) < len(recent_expressions):
                    self.logger.warning("Potential infinite loop detected")
                    break

        return current_expr, steps

    def _find_next_reduction(self, expr: LambdaExpression) -> Optional[Tuple[LambdaExpression, str]]:
        """Find next reduction based on strategy"""

        if self.strategy == ReductionStrategy.NORMAL_ORDER:
            return self._find_leftmost_outermost_reduction(expr)
        elif self.strategy == ReductionStrategy.APPLICATIVE_ORDER:
            return self._find_leftmost_innermost_reduction(expr)
        elif self.strategy == ReductionStrategy.TRINITY_ORDER:
            return self._find_trinity_guided_reduction(expr)
        else:
            return self._find_leftmost_outermost_reduction(expr)

    def _find_leftmost_outermost_reduction(self, expr: LambdaExpression) -> Optional[Tuple[LambdaExpression, str]]:
        """Find leftmost outermost reduction (normal order)"""

        if isinstance(expr, Application):
            # Check if function is abstraction (β-reduction possible)
            if isinstance(expr.function, Abstraction) and expr.function.body is not None:
                # Perform β-reduction
                reduced = expr.function.body.substitute(expr.function.parameter, expr.argument)
                return reduced, "β-reduction"

            # Try to reduce function first
            func_reduction = self._find_leftmost_outermost_reduction(expr.function)
            if func_reduction is not None:
                reduced_func, reduction_type = func_reduction
                return Application(function=reduced_func, argument=expr.argument), reduction_type

            # Then try to reduce argument
            arg_reduction = self._find_leftmost_outermost_reduction(expr.argument)
            if arg_reduction is not None:
                reduced_arg, reduction_type = arg_reduction
                return Application(function=expr.function, argument=reduced_arg), reduction_type

        elif isinstance(expr, Abstraction):
            # Try to reduce body
            if expr.body is not None:
                body_reduction = self._find_leftmost_outermost_reduction(expr.body)
                if body_reduction is not None:
                    reduced_body, reduction_type = body_reduction
                    return Abstraction(parameter=expr.parameter, body=reduced_body), reduction_type

        return None  # No reduction possible

    def _find_leftmost_innermost_reduction(self, expr: LambdaExpression) -> Optional[Tuple[LambdaExpression, str]]:
        """Find leftmost innermost reduction (applicative order)"""

        if isinstance(expr, Application):
            # First try to reduce argument
            if expr.argument is not None:
                arg_reduction = self._find_leftmost_innermost_reduction(expr.argument)
                if arg_reduction is not None:
                    reduced_arg, reduction_type = arg_reduction
                    return Application(function=expr.function, argument=reduced_arg), reduction_type

            # Then try to reduce function
            if expr.function is not None:
                func_reduction = self._find_leftmost_innermost_reduction(expr.function)
                if func_reduction is not None:
                    reduced_func, reduction_type = func_reduction
                    return Application(function=reduced_func, argument=expr.argument), reduction_type

            # Finally, if both are in normal form, try β-reduction
            if isinstance(expr.function, Abstraction) and expr.function.body is not None:
                reduced = expr.function.body.substitute(expr.function.parameter, expr.argument)
                return reduced, "β-reduction"

        elif isinstance(expr, Abstraction):
            # Try to reduce body
            if expr.body is not None:
                body_reduction = self._find_leftmost_innermost_reduction(expr.body)
                if body_reduction is not None:
                    reduced_body, reduction_type = body_reduction
                    return Abstraction(parameter=expr.parameter, body=reduced_body), reduction_type

        return None

    def _find_trinity_guided_reduction(self, expr: LambdaExpression) -> Optional[Tuple[LambdaExpression, str]]:
        """Find reduction guided by Trinity principles"""

        # Priority order: Truth > Goodness > Existence (for logical soundness)
        reductions = []

        # Collect all possible reductions with Trinity scores
        self._collect_trinity_reductions(expr, reductions, [])

        if not reductions:
            return None

        # Sort by Trinity score (higher is better)
        reductions.sort(key=lambda x: x[2], reverse=True)

        # Return best reduction
        reduced_expr, reduction_type, _ = reductions[0]
        return reduced_expr, reduction_type

    def _collect_trinity_reductions(self, expr: LambdaExpression, reductions: List, path: List[str]):
        """Collect all possible reductions with Trinity scores"""

        if isinstance(expr, Application):
            # β-reduction opportunity
            if isinstance(expr.function, Abstraction) and expr.function.body is not None:
                reduced = expr.function.body.substitute(expr.function.parameter, expr.argument)
                trinity_score = self._calculate_trinity_score(expr, reduced)
                reductions.append((reduced, "β-reduction", trinity_score))

            # Recurse into subexpressions
            if expr.function is not None:
                self._collect_trinity_reductions(expr.function, reductions, path + ["function"])
            if expr.argument is not None:
                self._collect_trinity_reductions(expr.argument, reductions, path + ["argument"])

        elif isinstance(expr, Abstraction):
            if expr.body is not None:
                self._collect_trinity_reductions(expr.body, reductions, path + ["body"])

    def _calculate_trinity_score(self, original: LambdaExpression, reduced: LambdaExpression) -> float:
        """Calculate Trinity score for reduction"""

        # Existence: Does reduction preserve essential structure?
        existence_score = 1.0 if len(reduced.free_variables()) <= len(original.free_variables()) else 0.5

        # Goodness: Does reduction simplify (reduce complexity)?
        original_complexity = self._calculate_complexity(original)
        reduced_complexity = self._calculate_complexity(reduced)
        goodness_score = 1.0 if reduced_complexity <= original_complexity else 0.3

        # Truth: Does reduction preserve logical validity?
        truth_score = 1.0  # Assume all valid λ-calculus reductions preserve truth

        # Weighted Trinity score
        return (existence_score * self.existence_weight +
                goodness_score * self.goodness_weight +
                truth_score * self.truth_weight)

    def _calculate_complexity(self, expr: LambdaExpression) -> int:
        """Calculate expression complexity"""

        if isinstance(expr, Variable):
            return 1
        elif isinstance(expr, Constant):
            return 1
        elif isinstance(expr, Abstraction):
            body_complexity = self._calculate_complexity(expr.body) if expr.body else 0
            return 2 + body_complexity  # λ and parameter add complexity
        elif isinstance(expr, Application):
            func_complexity = self._calculate_complexity(expr.function) if expr.function else 0
            arg_complexity = self._calculate_complexity(expr.argument) if expr.argument else 0
            return 1 + func_complexity + arg_complexity  # Application adds complexity
        elif isinstance(expr, TrinityCombinator):
            return 1  # Combinators are atomic
        else:
            return 0

# =========================================================================
# IV. LAMBDA ENGINE
# =========================================================================

class LambdaEngine:
    """Complete lambda calculus engine with Trinity grounding"""

    def __init__(self):
        self.reducer = LambdaReducer(ReductionStrategy.TRINITY_ORDER)
        self.principle_engine = PrincipleEngine()
        self.logger = logging.getLogger(__name__)

        # Expression cache for performance
        self.expression_cache: Dict[str, LambdaExpression] = {}
        self.reduction_cache: Dict[str, Tuple[LambdaExpression, List[ReductionStep]]] = {}

    def parse_expression(self, expression_string: str) -> Optional[LambdaExpression]:
        """Parse string into lambda expression (simplified parser)"""

        # Check cache first
        if expression_string in self.expression_cache:
            return self.expression_cache[expression_string]

        try:
            # Simplified parsing - would need full parser in practice
            expr_str = expression_string.strip()

            # Handle basic patterns
            if expr_str.startswith('#'):
                # Trinity combinator
                combinator_type = expr_str[1:]
                expr = TrinityCombinator(combinator_type)
            elif expr_str.isidentifier():
                # Variable
                expr = Variable(expr_str)
            elif expr_str.startswith('λ') or expr_str.startswith('\\'):
                # Abstraction (simplified)
                dot_pos = expr_str.find('.')
                if dot_pos > 0:
                    param = expr_str[1:dot_pos].strip()
                    body_str = expr_str[dot_pos+1:].strip()
                    body = self.parse_expression(body_str)
                    expr = Abstraction(parameter=param, body=body)
                else:
                    return None
            else:
                # Try to parse as constant
                try:
                    value = eval(expr_str)  # Dangerous - use proper parser in practice
                    expr = Constant(value=value, value_type=type(value).__name__)
                except:
                    return None

            # Cache result
            self.expression_cache[expression_string] = expr
            return expr

        except Exception as e:
            self.logger.error(f"Error parsing expression '{expression_string}': {e}")
            return None

    def evaluate(self, expression: Union[str, LambdaExpression]) -> Dict[str, Any]:
        """Evaluate lambda expression with Trinity grounding"""

        # Parse if string
        if isinstance(expression, str):
            expr = self.parse_expression(expression)
            if expr is None:
                return {"error": "Failed to parse expression"}
        else:
            expr = expression

        expr_string = expr.to_string()

        # Check reduction cache
        if expr_string in self.reduction_cache:
            normal_form, steps = self.reduction_cache[expr_string]
        else:
            # Perform reduction
            normal_form, steps = self.reducer.reduce(expr)
            self.reduction_cache[expr_string] = (normal_form, steps)

        # Validate with principles
        validation_result = self._validate_expression(expr)

        return {
            "original_expression": expr.to_string(),
            "normal_form": normal_form.to_string(),
            "reduction_steps": len(steps),
            "step_details": [step.to_dict() for step in steps],
            "trinity_grounding": {
                "existence": expr.trinity_grounding.existence,
                "goodness": expr.trinity_grounding.goodness,
                "truth": expr.trinity_grounding.truth,
                "trinity_product": expr.trinity_grounding.trinity_product()
            },
            "validation": validation_result,
            "complexity": self.reducer._calculate_complexity(expr),
            "free_variables": list(expr.free_variables()),
            "evaluation_timestamp": time.time()
        }

    def _validate_expression(self, expr: LambdaExpression) -> Dict[str, Any]:
        """Validate expression against Trinity principles"""

        operation_data = {
            "entity": "lambda_expression",
            "operation": "evaluate",
            "proposition": expr.to_string(),
            "context": {
                "expression_type": type(expr).__name__,
                "trinity_grounding": expr.trinity_grounding.to_tuple()
            }
        }

        return self.principle_engine.evaluate_operation(operation_data)

    def create_trinity_expression(self, existence_expr: str, goodness_expr: str, truth_expr: str) -> LambdaExpression:
        """Create Trinity-structured lambda expression"""

        # Parse component expressions
        e_expr = self.parse_expression(existence_expr)
        g_expr = self.parse_expression(goodness_expr)
        t_expr = self.parse_expression(truth_expr)

        if not all([e_expr, g_expr, t_expr]):
            raise ValueError("Failed to parse one or more Trinity expressions")

        # Create Trinity combinator application
        trinity_combinator = TrinityCombinator("TRINITY")

        # Apply Trinity combinator: TRINITY e_expr g_expr t_expr
        result = Application(
            function=Application(
                function=Application(
                    function=trinity_combinator,
                    argument=e_expr
                ),
                argument=g_expr
            ),
            argument=t_expr
        )

        # Set Trinity grounding
        result.trinity_grounding = TrinityVector(1/3, 1/3, 1/3)

        return result

    def get_statistics(self) -> Dict[str, Any]:
        """Get engine statistics"""

        return {
            "expression_cache_size": len(self.expression_cache),
            "reduction_cache_size": len(self.reduction_cache),
            "reduction_strategy": self.reducer.strategy.value,
            "max_reduction_steps": self.reducer.max_steps,
            "trinity_weights": {
                "existence": self.reducer.existence_weight,
                "goodness": self.reducer.goodness_weight,
                "truth": self.reducer.truth_weight
            }
        }

# =========================================================================
# V. MODULE EXPORTS
# =========================================================================

__all__ = [
    'ExpressionType',
    'LambdaExpression',
    'Variable',
    'Abstraction',
    'Application',
    'Constant',
    'TrinityCombinator',
    'ReductionStrategy',
    'ReductionStep',
    'LambdaReducer',
    'LambdaEngine'
]

# Create global lambda engine instance
_global_lambda_engine = None

def get_global_lambda_engine() -> LambdaEngine:
    """Get the global lambda engine instance"""
    global _global_lambda_engine
    if _global_lambda_engine is None:
        _global_lambda_engine = LambdaEngine()
    return _global_lambda_engine

def evaluate_lambda_expression(expression: str) -> Dict[str, Any]:
    """High-level API for lambda expression evaluation"""

    engine = get_global_lambda_engine()
    return engine.evaluate(expression)

# --- END OF FILE core/lambda_calculus.py ---
