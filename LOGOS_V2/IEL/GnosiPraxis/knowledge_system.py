"""
Knowledge Systems Framework

Provides classes for representing, managing, and reasoning
about knowledge in formal and informal systems.
"""

from typing import Dict, List, Any, Optional, Set, Tuple, Callable
from dataclasses import dataclass
from enum import Enum
import hashlib

class KnowledgeType(Enum):
    FACTUAL = "factual"
    PROCEDURAL = "procedural"
    CONCEPTUAL = "conceptual"
    METACOGNITIVE = "metacognitive"

class JustificationType(Enum):
    EMPIRICAL = "empirical"
    LOGICAL = "logical"
    AUTHORITATIVE = "authoritative"
    CONSENSUAL = "consensual"

@dataclass
class KnowledgeItem:
    """Represents a piece of knowledge."""
    content: Any
    knowledge_type: KnowledgeType
    confidence: float
    justification: JustificationType
    sources: List[str]
    prerequisites: Set[str] = None
    implications: Set[str] = None

    def __post_init__(self):
        if self.prerequisites is None:
            self.prerequisites = set()
        if self.implications is None:
            self.implications = set()

    @property
    def id(self) -> str:
        """Generate unique ID for this knowledge item."""
        content_str = str(self.content)
        return hashlib.md5(content_str.encode()).hexdigest()[:8]

class KnowledgeSystem:
    """
    System for managing and reasoning about knowledge.

    Supports knowledge representation, validation, inference,
    and knowledge graph construction.
    """

    def __init__(self):
        self.knowledge_base: Dict[str, KnowledgeItem] = {}
        self.knowledge_graph: Dict[str, Set[str]] = {}
        self.inference_rules: List[Callable] = []
        self.validation_functions: Dict[str, Callable] = {}

    def add_knowledge(self, item: KnowledgeItem) -> str:
        """Add knowledge item to the system."""
        item_id = item.id
        self.knowledge_base[item_id] = item

        # Update knowledge graph
        if item_id not in self.knowledge_graph:
            self.knowledge_graph[item_id] = set()

        # Add prerequisite relationships
        for prereq in item.prerequisites:
            if prereq in self.knowledge_base:
                if prereq not in self.knowledge_graph:
                    self.knowledge_graph[prereq] = set()
                self.knowledge_graph[prereq].add(item_id)

        # Add implication relationships
        for impl in item.implications:
            if impl not in self.knowledge_graph:
                self.knowledge_graph[impl] = set()
            self.knowledge_graph[item_id].add(impl)

        return item_id

    def get_knowledge(self, item_id: str) -> Optional[KnowledgeItem]:
        """Retrieve knowledge item by ID."""
        return self.knowledge_base.get(item_id)

    def validate_knowledge(self, item_id: str) -> Dict[str, Any]:
        """Validate a knowledge item."""
        if item_id not in self.knowledge_base:
            return {"valid": False, "reason": "Knowledge item not found"}

        item = self.knowledge_base[item_id]

        validation_results = {
            "justification_check": self._validate_justification(item),
            "consistency_check": self._check_consistency(item),
            "prerequisite_check": self._check_prerequisites(item),
            "confidence_assessment": self._assess_confidence(item)
        }

        overall_valid = all(result for result in validation_results.values()
                          if isinstance(result, bool))

        return {
            "valid": overall_valid,
            "details": validation_results
        }

    def _validate_justification(self, item: KnowledgeItem) -> bool:
        """Validate knowledge justification."""
        if item.justification == JustificationType.EMPIRICAL:
            return len(item.sources) > 0
        elif item.justification == JustificationType.LOGICAL:
            return len(item.prerequisites) > 0
        elif item.justification == JustificationType.AUTHORITATIVE:
            return len(item.sources) > 0
        elif item.justification == JustificationType.CONSENSUAL:
            return len(item.sources) >= 3  # Requires multiple sources
        return False

    def _check_consistency(self, item: KnowledgeItem) -> bool:
        """Check knowledge consistency."""
        # Simplified consistency check
        return item.confidence >= 0.0 and item.confidence <= 1.0

    def _check_prerequisites(self, item: KnowledgeItem) -> bool:
        """Check if prerequisites are satisfied."""
        for prereq_id in item.prerequisites:
            if prereq_id not in self.knowledge_base:
                return False
            prereq = self.knowledge_base[prereq_id]
            if not self.validate_knowledge(prereq_id)["valid"]:
                return False
        return True

    def _assess_confidence(self, item: KnowledgeItem) -> float:
        """Assess confidence in knowledge item."""
        base_confidence = item.confidence

        # Adjust based on justification strength
        justification_multiplier = {
            JustificationType.EMPIRICAL: 1.0,
            JustificationType.LOGICAL: 0.9,
            JustificationType.AUTHORITATIVE: 0.8,
            JustificationType.CONSENSUAL: 0.7
        }

        return min(1.0, base_confidence * justification_multiplier[item.justification])

    def infer_new_knowledge(self) -> List[KnowledgeItem]:
        """Apply inference rules to generate new knowledge."""
        new_knowledge = []

        for rule in self.inference_rules:
            try:
                inferred = rule(self.knowledge_base)
                if inferred:
                    new_knowledge.extend(inferred)
            except Exception:
                continue

        # Add inferred knowledge to system
        for item in new_knowledge:
            self.add_knowledge(item)

        return new_knowledge

    def get_knowledge_chain(self, item_id: str) -> List[str]:
        """Get prerequisite chain for knowledge item."""
        if item_id not in self.knowledge_base:
            return []

        chain = []
        visited = set()
        to_visit = [item_id]

        while to_visit:
            current = to_visit.pop()
            if current in visited:
                continue

            visited.add(current)
            chain.append(current)

            if current in self.knowledge_base:
                item = self.knowledge_base[current]
                to_visit.extend(item.prerequisites - visited)

        return chain[::-1]  # Reverse to show dependencies first

    def search_knowledge(self, query: str, knowledge_type: Optional[KnowledgeType] = None) -> List[str]:
        """Search knowledge base for items matching query."""
        results = []

        for item_id, item in self.knowledge_base.items():
            if knowledge_type and item.knowledge_type != knowledge_type:
                continue

            content_str = str(item.content).lower()
            if query.lower() in content_str:
                results.append(item_id)

        return results

    def get_knowledge_statistics(self) -> Dict[str, Any]:
        """Get statistics about the knowledge base."""
        type_counts = {}
        justification_counts = {}
        total_confidence = 0.0

        for item in self.knowledge_base.values():
            type_counts[item.knowledge_type] = type_counts.get(item.knowledge_type, 0) + 1
            justification_counts[item.justification] = justification_counts.get(item.justification, 0) + 1
            total_confidence += item.confidence

        return {
            "total_items": len(self.knowledge_base),
            "type_distribution": type_counts,
            "justification_distribution": justification_counts,
            "average_confidence": total_confidence / len(self.knowledge_base) if self.knowledge_base else 0.0,
            "graph_nodes": len(self.knowledge_graph),
            "graph_edges": sum(len(edges) for edges in self.knowledge_graph.values())
        }