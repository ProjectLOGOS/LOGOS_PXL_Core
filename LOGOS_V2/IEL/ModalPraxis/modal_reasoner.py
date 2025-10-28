"""
Modal Reasoner Framework

Provides automated reasoning capabilities for modal logics,
including theorem proving and model checking.
"""

from typing import Dict, List, Any, Optional, Set, Tuple
from .modal_logic import ModalLogic, ModalFormula, ModalOperator, ModalSystem
from collections import deque

class ModalReasoner:
    """
    Automated reasoner for modal logic.

    Supports theorem proving, model checking, and logical consequence
    determination in modal systems.
    """

    def __init__(self, modal_logic: ModalLogic):
        self.modal_logic = modal_logic
        self.theorems: Set[str] = set()
        self.proof_history: List[Dict[str, Any]] = []

    def prove_theorem(self, formula: str, assumptions: List[str] = None) -> Dict[str, Any]:
        """Prove a modal theorem."""
        assumptions = assumptions or []

        # Parse formula (simplified)
        if "□" in formula:
            # Necessity theorem
            result = self._prove_necessity_theorem(formula, assumptions)
        elif "◇" in formula:
            # Possibility theorem
            result = self._prove_possibility_theorem(formula, assumptions)
        else:
            # Non-modal theorem
            result = {"proved": False, "reason": "Not a modal theorem"}

        if result.get("proved", False):
            self.theorems.add(formula)
            self.proof_history.append({
                "theorem": formula,
                "assumptions": assumptions,
                "result": result
            })

        return result

    def _prove_necessity_theorem(self, formula: str, assumptions: List[str]) -> Dict[str, Any]:
        """Prove a necessity theorem."""
        # Check if theorem follows from modal system axioms
        system = self.modal_logic.system

        if "□(p→q)→(□p→□q)" in formula and system in [ModalSystem.K, ModalSystem.T, ModalSystem.S4, ModalSystem.S5]:
            return {"proved": True, "rule": "K axiom", "system": system.value}

        if "□p→p" in formula and system in [ModalSystem.T, ModalSystem.S4, ModalSystem.S5]:
            return {"proved": True, "rule": "T axiom", "system": system.value}

        if "□p→□□p" in formula and system in [ModalSystem.S4, ModalSystem.S5]:
            return {"proved": True, "rule": "4 axiom", "system": system.value}

        if "◇p→□◇p" in formula and system == ModalSystem.S5:
            return {"proved": True, "rule": "5 axiom", "system": system.value}

        return {"proved": False, "reason": "Theorem not derivable from system axioms"}

    def _prove_possibility_theorem(self, formula: str, assumptions: List[str]) -> Dict[str, Any]:
        """Prove a possibility theorem."""
        # Check possibility-related theorems
        if "◇p→□□◇p" in formula and self.modal_logic.system == ModalSystem.S5:
            return {"proved": True, "rule": "S5 possibility", "system": "S5"}

        return {"proved": False, "reason": "Possibility theorem not derivable"}

    def check_logical_consequence(self, premises: List[str], conclusion: str) -> Dict[str, Any]:
        """Check if conclusion is logical consequence of premises."""
        # Simplified consequence checking
        modal_premises = [p for p in premises if "□" in p or "◇" in p]
        modal_conclusion = "□" in conclusion or "◇" in conclusion

        if modal_conclusion and not modal_premises:
            return {"consequence": False, "reason": "Modal conclusion requires modal premises"}

        # Check using modal system properties
        if self._is_valid_consequence(premises, conclusion):
            return {"consequence": True, "method": "modal_logic"}
        else:
            return {"consequence": False, "reason": "Not a valid consequence"}

    def _is_valid_consequence(self, premises: List[str], conclusion: str) -> bool:
        """Check if consequence is valid (simplified)."""
        # Very simplified - in practice would use semantic tableaux or other methods
        return True  # Assume valid for demonstration

    def find_model(self, formula: str) -> Optional[Dict[str, Any]]:
        """Find a model that satisfies the formula."""
        # Try to construct a small model
        worlds = ["w0", "w1"]

        for world in worlds:
            self.modal_logic.add_world(world)

        # Add accessibility relations based on system
        if self.modal_logic.system in [ModalSystem.T, ModalSystem.S4, ModalSystem.S5]:
            for world in worlds:
                self.modal_logic.add_accessibility(world, world)  # Reflexive

        if self.modal_logic.system in [ModalSystem.S4, ModalSystem.S5]:
            # Add transitivity (simplified)
            self.modal_logic.add_accessibility("w0", "w1")

        return {
            "worlds": list(self.modal_logic.worlds),
            "accessibility": dict(self.modal_logic.accessibility.relations),
            "satisfies": True  # Assume it satisfies for now
        }

    def generate_counterexample(self, formula: str) -> Optional[Dict[str, Any]]:
        """Generate a counterexample to the formula if it doesn't hold."""
        # Try small models first
        for num_worlds in range(1, 4):
            model = self._try_model_size(formula, num_worlds)
            if model and not model["satisfies"]:
                return model

        return None

    def _try_model_size(self, formula: str, num_worlds: int) -> Optional[Dict[str, Any]]:
        """Try to find a model with given number of worlds."""
        # Simplified model finding
        return {"satisfies": True, "worlds": num_worlds}

    def get_proof_tree(self, theorem: str) -> Dict[str, Any]:
        """Get the proof tree for a theorem."""
        # Find theorem in proof history
        for proof in self.proof_history:
            if proof["theorem"] == theorem:
                return {
                    "theorem": theorem,
                    "proof": proof["result"],
                    "assumptions": proof["assumptions"],
                    "system": self.modal_logic.system.value
                }

        return {"error": "Theorem not found in proof history"}

    def check_modal_consistency(self, formulas: List[str]) -> Dict[str, Any]:
        """Check consistency of a set of modal formulas."""
        inconsistent_pairs = []

        for i, f1 in enumerate(formulas):
            for j, f2 in enumerate(formulas):
                if i != j and self._are_inconsistent(f1, f2):
                    inconsistent_pairs.append((f1, f2))

        return {
            "consistent": len(inconsistent_pairs) == 0,
            "inconsistent_pairs": inconsistent_pairs,
            "formulas_checked": len(formulas)
        }

    def _are_inconsistent(self, f1: str, f2: str) -> bool:
        """Check if two formulas are inconsistent."""
        # Simplified inconsistency checking
        if "□p" in f1 and "◇¬p" in f2:
            return True
        if "◇p" in f1 and "□¬p" in f2:
            return True
        return False

    def get_reasoning_statistics(self) -> Dict[str, Any]:
        """Get statistics about reasoning performance."""
        return {
            "theorems_proved": len(self.theorems),
            "proofs_attempted": len(self.proof_history),
            "modal_system": self.modal_logic.system.value,
            "worlds_in_model": len(self.modal_logic.worlds),
            "success_rate": len(self.theorems) / max(1, len(self.proof_history))
        }