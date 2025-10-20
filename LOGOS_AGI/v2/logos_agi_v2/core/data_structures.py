"""Shared Data Structures

Common data structures and utility types for THŌNOC system.
Provides shared type definitions, processing results, and data containers
used across multiple components.

Dependencies: typing, enum, dataclasses
"""

from typing import Dict, List, Tuple, Optional, Union, Any
from enum import Enum
from dataclasses import dataclass, field


class OntologicalType(Enum):
    """Ontological dimensions in trinitarian framework."""
    EXISTENCE = "𝔼"
    GOODNESS = "𝔾"
    TRUTH = "𝕋"
    PROP = "Prop"  # Propositional type


class FunctionType:
    """Function type constructor."""
    
    def __init__(self, domain: OntologicalType, codomain: Union[OntologicalType, 'FunctionType']):
        """Initialize function type.
        
        Args:
            domain: Input type
            codomain: Output type
        """
        self.domain = domain
        self.codomain = codomain
    
    def __str__(self) -> str:
        """Return string representation."""
        domain_str = self.domain.value
        codomain_str = str(self.codomain)
        return f"{domain_str} → {codomain_str}"
    
    def __eq__(self, other) -> bool:
        """Check equality with another type."""
        if not isinstance(other, FunctionType):
            return False
        return (self.domain == other.domain and
                self.codomain == other.codomain)


class ModalStatus(Enum):
    """Modal status classifications."""
    NECESSARY = "necessary"
    ACTUAL = "actual"
    POSSIBLE = "possible"
    IMPOSSIBLE = "impossible"
    UNKNOWN = "unknown"


@dataclass
class FractalPosition:
    """Position in fractal space."""
    c_real: float
    c_imag: float
    iterations: int
    in_set: bool
    final_z: Tuple[float, float] = field(default_factory=lambda: (0.0, 0.0))
    escape_radius: float = 2.0
    
    @property
    def complex(self) -> complex:
        """Get position as complex number."""
        return complex(self.c_real, self.c_imag)
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary representation."""
        return {
            "c_real": self.c_real,
            "c_imag": self.c_imag,
            "iterations": self.iterations,
            "in_set": self.in_set,
            "final_z": self.final_z,
            "escape_radius": self.escape_radius
        }
    
    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'FractalPosition':
        """Create from dictionary representation."""
        return cls(
            c_real=data.get("c_real", 0.0),
            c_imag=data.get("c_imag", 0.0),
            iterations=data.get("iterations", 0),
            in_set=data.get("in_set", False),
            final_z=data.get("final_z", (0.0, 0.0)),
            escape_radius=data.get("escape_radius", 2.0)
        )


@dataclass
class ProcessingResult:
    """Result of query processing."""
    query: str
    trinity_vector: Tuple[float, float, float]
    modal_status: ModalStatus
    coherence: float
    fractal_position: FractalPosition
    lambda_expr: Optional[Any] = None
    entailments: List[Any] = field(default_factory=list)
    summary: str = ""
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary representation."""
        return {
            "query": self.query,
            "trinity_vector": self.trinity_vector,
            "modal_status": self.modal_status.value,
            "coherence": self.coherence,
            "fractal_position": self.fractal_position.to_dict(),
            "lambda_expr": str(self.lambda_expr) if self.lambda_expr else None,
            "entailments": [str(e) for e in self.entailments],
            "summary": self.summary
        }
    
    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'ProcessingResult':
        """Create from dictionary representation."""
        fractal_pos_data = data.get("fractal_position", {})
        
        return cls(
            query=data.get("query", ""),
            trinity_vector=data.get("trinity_vector", (0.5, 0.5, 0.5)),
            modal_status=ModalStatus(data.get("modal_status", "unknown")),
            coherence=data.get("coherence", 0.0),
            fractal_position=FractalPosition.from_dict(fractal_pos_data),
            lambda_expr=None,  # Cannot reconstruct lambda expression from string
            entailments=[],    # Cannot reconstruct entailments
            summary=data.get("summary", "")
        )


@dataclass
class OntologicalRelation:
    """Relation between ontological nodes."""
    source_id: str
    target_id: str
    relation_type: str
    strength: float
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary representation."""
        return {
            "source_id": self.source_id,
            "target_id": self.target_id,
            "relation_type": self.relation_type,
            "strength": self.strength,
            "metadata": self.metadata
        }
    
    @classmethod
    def from_dict(cls, data: Dict[str, Any]) -> 'OntologicalRelation':
        """Create from dictionary representation."""
        return cls(
            source_id=data.get("source_id", ""),
            target_id=data.get("target_id", ""),
            relation_type=data.get("relation_type", ""),
            strength=data.get("strength", 0.0),
            metadata=data.get("metadata", {})
        )


def format_trinity_vector(trinity: Tuple[float, float, float]) -> str:
    """Format trinity vector as string.
    
    Args:
        trinity: Trinity vector (existence, goodness, truth)
        
    Returns:
        Formatted string representation
    """
    e, g, t = trinity
    return f"(E={e:.3f}, G={g:.3f}, T={t:.3f})"


def format_modal_status(status: ModalStatus, coherence: float) -> str:
    """Format modal status as string with coherence.
    
    Args:
        status: Modal status
        coherence: Coherence value
        
    Returns:
        Formatted string representation
    """
    if status == ModalStatus.NECESSARY:
        icon = "□"  # Box
    elif status == ModalStatus.POSSIBLE:
        icon = "◇"  # Diamond
    elif status == ModalStatus.ACTUAL:
        icon = "A"  # Actuality
    elif status == ModalStatus.IMPOSSIBLE:
        icon = "¬◇"  # Negated diamond
    else:
        icon = "?"
    
    return f"{icon} {status.value.capitalize()} (coherence: {coherence:.3f})"