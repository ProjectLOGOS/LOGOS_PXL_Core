"""
Universal Logic Framework

Provides logical frameworks for universal reasoning,
including modal logic for necessity/contingency and
universal quantification over domains.
"""

from typing import Set, Dict, List, Any, Optional, Callable
from enum import Enum

class Modality(Enum):
    NECESSARY = "□"
    POSSIBLE = "◇"
    CONTINGENT = "△"
    IMPOSSIBLE = "⊥"

class UniversalLogic:
    """
    Framework for universal logical reasoning.

    Supports modal logic, universal quantification, and
    reasoning about necessary/contingent truths.
    """

    def __init__(self, domain: Set[Any] = None):
        """
        Initialize universal logic system.

        Args:
            domain: Universal domain of discourse
        """
        self.domain = domain or set()
        self.axioms: Dict[str, bool] = {}
        self.theorems: Dict[str, Dict[str, Any]] = {}
        self.modal_operators = {
            Modality.NECESSARY: self._necessary,
            Modality.POSSIBLE: self._possible,
            Modality.CONTINGENT: self._contingent,
            Modality.IMPOSSIBLE: self._impossible
        }

    def add_axiom(self, axiom: str, value: bool = True):
        """Add an axiom to the system."""
        self.axioms[axiom] = value

    def add_theorem(self, theorem: str, proof: List[str] = None, modality: Modality = None):
        """Add a theorem with optional proof and modality."""
        self.theorems[theorem] = {
            'proved': proof is not None,
            'proof': proof or [],
            'modality': modality,
            'verified': False
        }

    def apply_modal_operator(self, proposition: str, modality: Modality) -> bool:
        """Apply modal operator to a proposition."""
        if modality in self.modal_operators:
            return self.modal_operators[modality](proposition)
        return False

    def _necessary(self, proposition: str) -> bool:
        """Check if proposition is necessary (true in all worlds)."""
        # Simplified - in practice would check all accessible worlds
        return proposition in self.axioms and self.axioms[proposition]

    def _possible(self, proposition: str) -> bool:
        """Check if proposition is possible (true in some world)."""
        return True  # Simplified - assume possibility unless proven impossible

    def _contingent(self, proposition: str) -> bool:
        """Check if proposition is contingent (neither necessary nor impossible)."""
        return not self._necessary(proposition) and not self._impossible(proposition)

    def _impossible(self, proposition: str) -> bool:
        """Check if proposition is impossible."""
        return False  # Simplified - no impossibilities assumed

    def universal_quantification(self, predicate: Callable[[Any], bool]) -> bool:
        """Check if predicate holds for all elements in domain."""
        return all(predicate(element) for element in self.domain)

    def existential_quantification(self, predicate: Callable[[Any], bool]) -> bool:
        """Check if predicate holds for some element in domain."""
        return any(predicate(element) for element in self.domain)

    def get_logical_status(self, proposition: str) -> Dict[str, Any]:
        """Get the logical status of a proposition."""
        return {
            'necessary': self._necessary(proposition),
            'possible': self._possible(proposition),
            'contingent': self._contingent(proposition),
            'impossible': self._impossible(proposition),
            'in_theorems': proposition in self.theorems
        }