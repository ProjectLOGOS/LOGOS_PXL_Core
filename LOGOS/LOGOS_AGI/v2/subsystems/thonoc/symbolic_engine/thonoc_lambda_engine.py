from typing import Dict, List, Tuple, Optional, Union, Any, Callable
from enum import Enum
import logging


class OntologicalType(Enum):
    EXISTENCE = "EXISTENCE"
    GOODNESS = "GOODNESS"
    TRUTH = "TRUTH"
    PROP = "PROP"


class LogosExpr:
    def __str__(self):
        return "LogosExpr"


class Variable(LogosExpr):
    def __init__(self, name: str, onto_type: str):
        self.name, self.onto_type = name, OntologicalType[onto_type]

    def __str__(self):
        return f"{self.name}:{self.onto_type.name}"


class Value(LogosExpr):
    def __init__(self, value: str, onto_type: str):
        self.value, self.onto_type = value, OntologicalType[onto_type]

    def __str__(self):
        return f"{self.value}:{self.onto_type.name}"


class Abstraction(LogosExpr):
    def __init__(self, var_name: str, var_type: str, body: LogosExpr):
        self.var_name, self.var_type, self.body = var_name, OntologicalType[var_type], body

    def __str__(self):
        return f"λ{self.var_name}:{self.var_type.name}.({self.body})"


class Application(LogosExpr):
    def __init__(self, func: LogosExpr, arg: LogosExpr):
        self.func, self.arg = func, arg

    def __str__(self):
        return f"({self.func} {self.arg})"


class LambdaEngine:
    def __init__(self):
        self.evaluator = self.Evaluator(self)

    def substitute(self, expr, var_name, value):
        if isinstance(expr, Variable):
            return value if expr.name == var_name else expr
        if isinstance(expr, Value):
            return expr
        if isinstance(expr, Abstraction):
            if expr.var_name == var_name:
                return expr
            return Abstraction(
                expr.var_name, expr.var_type.name, self.substitute(expr.body, var_name, value)
            )
        if isinstance(expr, Application):
            return Application(
                self.substitute(expr.func, var_name, value),
                self.substitute(expr.arg, var_name, value),
            )
        return expr

    class Evaluator:
        def __init__(self, engine):
            self.engine = engine

        def evaluate(self, expr):
            if isinstance(expr, Application):
                func = self.evaluate(expr.func)
                arg = self.evaluate(expr.arg)
                if isinstance(func, Abstraction):
                    return self.evaluate(self.engine.substitute(func.body, func.var_name, arg))
                return Application(func, arg)
            if isinstance(expr, Abstraction):
                return Abstraction(expr.var_name, expr.var_type.name, self.evaluate(expr.body))
            return expr

    def evaluate(self, expr):
        return self.evaluator.evaluate(expr)
