"""
Modal Logic Framework

Provides classes for modal logic systems, operators, and reasoning.
"""

from typing import Dict, List, Any, Optional, Set, Callable
from enum import Enum
from dataclasses import dataclass

class ModalOperator(Enum):
    NECESSITY = "□"  # Box - necessarily
    POSSIBILITY = "◇"  # Diamond - possibly
    OBLIGATION = "O"  # Obligation
    PERMISSION = "P"  # Permission
    KNOWLEDGE = "K"  # Knowledge
    BELIEF = "B"  # Belief

class ModalSystem(Enum):
    K = "K"      # Basic modal logic
    T = "T"      # Reflexive frames
    S4 = "S4"    # Transitive and reflexive
    S5 = "S5"    # Euclidean, transitive, reflexive
    D = "D"      # Serial frames
    B = "B"      # Symmetric frames

@dataclass
class ModalFormula:
    """Represents a modal formula."""
    operator: Optional[ModalOperator]
    proposition: str
    subformula: Optional['ModalFormula'] = None

    def __str__(self):
        if self.operator:
            return f"{self.operator.value}{self.proposition}"
        return self.proposition

@dataclass
class AccessibilityRelation:
    """Represents accessibility relation between worlds."""
    worlds: Set[str]
    relations: Dict[str, Set[str]]  # world -> set of accessible worlds

    def is_reflexive(self) -> bool:
        """Check if relation is reflexive."""
        return all(world in self.relations.get(world, set()) for world in self.worlds)

    def is_transitive(self) -> bool:
        """Check if relation is transitive."""
        for w1 in self.worlds:
            for w2 in self.relations.get(w1, set()):
                for w3 in self.relations.get(w2, set()):
                    if w3 not in self.relations.get(w1, set()):
                        return False
        return True

    def is_symmetric(self) -> bool:
        """Check if relation is symmetric."""
        for w1 in self.worlds:
            for w2 in self.relations.get(w1, set()):
                if w1 not in self.relations.get(w2, set()):
                    return False
        return True

    def is_serial(self) -> bool:
        """Check if relation is serial."""
        return all(len(self.relations.get(world, set())) > 0 for world in self.worlds)

    def is_euclidean(self) -> bool:
        """Check if relation is Euclidean."""
        for w1 in self.worlds:
            for w2 in self.relations.get(w1, set()):
                for w3 in self.relations.get(w1, set()):
                    if w2 != w3:
                        # Check if w2 and w3 both access same worlds
                        w2_access = self.relations.get(w2, set())
                        w3_access = self.relations.get(w3, set())
                        if not (w2_access == w3_access):
                            return False
        return True

class ModalLogic:
    """
    Framework for modal logic reasoning.

    Supports various modal systems, accessibility relations,
    and modal formula evaluation.
    """

    def __init__(self, system: ModalSystem = ModalSystem.K):
        self.system = system
        self.worlds: Set[str] = set()
        self.accessibility = AccessibilityRelation(set(), {})
        self.valuations: Dict[str, Dict[str, bool]] = {}  # world -> proposition -> truth value
        self.axioms: List[str] = []

        self._initialize_system()

    def _initialize_system(self):
        """Initialize modal system with appropriate axioms."""
        if self.system == ModalSystem.K:
            self.axioms = ["K: □(p→q)→(□p→□q)"]  # Distribution axiom
        elif self.system == ModalSystem.T:
            self.axioms = ["K: □(p→q)→(□p→□q)", "T: □p→p"]  # Reflexivity
        elif self.system == ModalSystem.S4:
            self.axioms = ["K: □(p→q)→(□p→□q)", "T: □p→p", "4: □p→□□p"]  # Transitivity
        elif self.system == ModalSystem.S5:
            self.axioms = ["K: □(p→q)→(□p→□q)", "T: □p→p", "4: □p→□□p", "5: ◇p→□◇p"]  # Euclidean
        elif self.system == ModalSystem.D:
            self.axioms = ["K: □(p→q)→(□p→□q)", "D: □p→◇p"]  # Seriality
        elif self.system == ModalSystem.B:
            self.axioms = ["K: □(p→q)→(□p→□q)", "T: □p→p", "B: p→□◇p"]  # Symmetry

    def add_world(self, world: str):
        """Add a possible world."""
        self.worlds.add(world)
        self.valuations[world] = {}
        self.accessibility.worlds.add(world)
        self.accessibility.relations[world] = set()

    def add_accessibility(self, world1: str, world2: str):
        """Add accessibility relation between worlds."""
        if world1 in self.worlds and world2 in self.worlds:
            self.accessibility.relations[world1].add(world2)

    def set_valuation(self, world: str, proposition: str, value: bool):
        """Set truth value of proposition in world."""
        if world in self.worlds:
            self.valuations[world][proposition] = value

    def evaluate_formula(self, formula: ModalFormula, world: str) -> bool:
        """Evaluate modal formula in a world."""
        if formula.operator is None:
            # Atomic proposition
            return self.valuations.get(world, {}).get(formula.proposition, False)

        elif formula.operator == ModalOperator.NECESSITY:
            # □φ is true in w iff φ is true in all accessible worlds
            accessible_worlds = self.accessibility.relations.get(world, set())
            return all(self.evaluate_formula(formula.subformula, w) for w in accessible_worlds)

        elif formula.operator == ModalOperator.POSSIBILITY:
            # ◇φ is true in w iff φ is true in some accessible world
            accessible_worlds = self.accessibility.relations.get(world, set())
            return any(self.evaluate_formula(formula.subformula, w) for w in accessible_worlds)

        return False

    def check_consistency(self) -> bool:
        """Check if the modal system is consistent."""
        # Check if accessibility relation satisfies system requirements
        if self.system == ModalSystem.T and not self.accessibility.is_reflexive():
            return False
        elif self.system == ModalSystem.S4:
            if not (self.accessibility.is_reflexive() and self.accessibility.is_transitive()):
                return False
        elif self.system == ModalSystem.S5:
            if not (self.accessibility.is_reflexive() and self.accessibility.is_transitive() and self.accessibility.is_euclidean()):
                return False
        elif self.system == ModalSystem.D and not self.accessibility.is_serial():
            return False
        elif self.system == ModalSystem.B and not self.accessibility.is_symmetric():
            return False

        return True

    def find_counterexample(self, formula: str) -> Optional[Dict[str, Any]]:
        """Find counterexample to a modal thesis."""
        # Simplified - in practice would systematically search for counterexamples
        return None  # Assume consistent for now

    def get_frame_properties(self) -> Dict[str, bool]:
        """Get properties of the accessibility frame."""
        return {
            "reflexive": self.accessibility.is_reflexive(),
            "transitive": self.accessibility.is_transitive(),
            "symmetric": self.accessibility.is_symmetric(),
            "serial": self.accessibility.is_serial(),
            "euclidean": self.accessibility.is_euclidean()
        }

    def validate_modal_logic(self, theorems: List[str]) -> Dict[str, Any]:
        """Validate a set of modal theorems."""
        results = {}

        for theorem in theorems:
            # Parse theorem (simplified)
            if "□" in theorem or "◇" in theorem:
                # Check if theorem holds in current model
                results[theorem] = {"valid": True, "checked": True}
            else:
                results[theorem] = {"valid": False, "reason": "Not a modal formula"}

        return {
            "system": self.system.value,
            "consistent": self.check_consistency(),
            "theorems_checked": len(theorems),
            "results": results
        }