"""
LOGOS AGI v1.0 Meta-Reasoning Module

Generates candidate IELs for new domains and maintains a verified IEL registry.
Enables autonomous reasoning extension while preserving formal verification guarantees.
"""

from .iel_generator import IELGenerator
from .iel_registry import IELRegistry

__all__ = ['IELGenerator', 'IELRegistry']
