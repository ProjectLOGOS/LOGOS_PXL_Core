"""
IEL Runtime Interface - Python bridge to verified modal logic evaluation

This module provides a Python interface to the formally verified modal logic
and IEL (Identity-Experiential Logic) evaluation engine extracted from Coq proofs.
"""

import json
import logging
import os
import subprocess
import tempfile
from typing import Dict, List, Tuple, Any, Optional, Union
from pathlib import Path
import ctypes
from ctypes import cdll, c_char_p, c_int, c_bool

logger = logging.getLogger(__name__)

class ProofBridgeError(Exception):
    """Raised when proof bridge operations fail"""
    pass

class ModalLogicEvaluator:
    """
    Python interface to verified modal logic evaluation engine

    This class provides access to formally verified modal logic evaluation
    capabilities extracted from Coq proofs via OCaml, including countermodel
    generation for falsifiability analysis.
    """

    def __init__(self, bridge_path: Optional[str] = None):
        """
        Initialize the modal logic evaluator

        Args:
            bridge_path: Path to compiled OCaml bridge library. If None,
                        uses default path relative to this module.
        """
        self.bridge_path = bridge_path or self._get_default_bridge_path()
        self._bridge_lib = None
        self._initialize_bridge()
        self.countermodel_generation_enabled = True

    def _get_default_bridge_path(self) -> str:
        """Get default path to the compiled bridge library"""
        current_dir = Path(__file__).parent
        return str(current_dir / "proof_bridge.so")

    def _initialize_bridge(self):
        """Initialize the OCaml bridge library"""
        try:
            if not os.path.exists(self.bridge_path):
                logger.warning(f"Bridge library not found at {self.bridge_path}")
                logger.info("Falling back to subprocess interface")
                self._bridge_lib = None
                return

            # Load the compiled OCaml library
            self._bridge_lib = cdll.LoadLibrary(self.bridge_path)

            # Configure function signatures
            self._bridge_lib.eval_modal_string.argtypes = [
                c_char_p, c_char_p, c_char_p, c_char_p
            ]
            self._bridge_lib.eval_modal_string.restype = c_char_p

            logger.info("OCaml bridge library loaded successfully")

        except Exception as e:
            logger.warning(f"Failed to load OCaml bridge: {e}")
            logger.info("Falling back to subprocess interface")
            self._bridge_lib = None

    def evaluate_modal_proposition(
        self,
        proposition: str,
        world: str = "w0",
        accessible_worlds: Optional[List[str]] = None,
        valuations: Optional[Dict[str, bool]] = None,
        generate_countermodel: bool = True
    ) -> Dict[str, Any]:
        """
        Evaluate a modal logic proposition in a given Kripke model

        Args:
            proposition: Modal logic formula as string (e.g., "[]p -> p", "<>q && r")
            world: Current world identifier
            accessible_worlds: List of accessible world identifiers
            valuations: Dictionary mapping atomic propositions to truth values
            generate_countermodel: Whether to generate countermodels for false propositions

        Returns:
            Dictionary containing evaluation result, metadata, and optional countermodel

        Example:
            >>> evaluator = ModalLogicEvaluator()
            >>> result = evaluator.evaluate_modal_proposition(
            ...     "[]p -> p",
            ...     world="w0",
            ...     accessible_worlds=["w0", "w1"],
            ...     valuations={"p": True}
            ... )
            >>> print(result["result"])  # True
        """
        if accessible_worlds is None:
            accessible_worlds = [world]
        if valuations is None:
            valuations = {}

        try:
            if self._bridge_lib:
                result = self._evaluate_via_library(
                    proposition, world, accessible_worlds, valuations
                )
            else:
                result = self._evaluate_via_subprocess(
                    proposition, world, accessible_worlds, valuations
                )

            # Generate countermodel if evaluation failed and countermodel generation is enabled
            if (not result.get("result", False) and
                result.get("success", False) and
                generate_countermodel and
                self.countermodel_generation_enabled):
                countermodel = self._generate_countermodel(
                    proposition, world, accessible_worlds, valuations
                )
                result["countermodel"] = countermodel
                result["falsified_by"] = countermodel

            return result

        except Exception as e:
            logger.error(f"Modal logic evaluation failed: {e}")
            return {
                "success": False,
                "error": str(e),
                "proposition": proposition
            }

    def _evaluate_via_library(
        self,
        proposition: str,
        world: str,
        accessible_worlds: List[str],
        valuations: Dict[str, bool]
    ) -> Dict[str, Any]:
        """Evaluate using direct library calls"""
        world_c = c_char_p(world.encode('utf-8'))
        accessible_c = c_char_p(json.dumps(accessible_worlds).encode('utf-8'))
        valuations_c = c_char_p(json.dumps(valuations).encode('utf-8'))
        proposition_c = c_char_p(proposition.encode('utf-8'))

        result_ptr = self._bridge_lib.eval_modal_string(
            world_c, accessible_c, valuations_c, proposition_c
        )

        if not result_ptr:
            raise ProofBridgeError("Bridge library returned null result")

        result_json = ctypes.string_at(result_ptr).decode('utf-8')
        return json.loads(result_json)

    def _evaluate_via_subprocess(
        self,
        proposition: str,
        world: str,
        accessible_worlds: List[str],
        valuations: Dict[str, bool]
    ) -> Dict[str, Any]:
        """Evaluate using subprocess call to OCaml executable"""
        # Create temporary input file
        input_data = {
            "proposition": proposition,
            "world": world,
            "accessible_worlds": accessible_worlds,
            "valuations": valuations
        }

        with tempfile.NamedTemporaryFile(mode='w', suffix='.json', delete=False) as f:
            json.dump(input_data, f)
            input_file = f.name

        try:
            # Call OCaml evaluator
            bridge_exe = self.bridge_path.replace('.so', '.exe')
            if not os.path.exists(bridge_exe):
                bridge_exe = str(Path(__file__).parent / "proof_bridge_cli.exe")

            result = subprocess.run(
                [bridge_exe, input_file],
                capture_output=True,
                text=True,
                timeout=30
            )

            if result.returncode != 0:
                raise ProofBridgeError(f"Bridge process failed: {result.stderr}")

            return json.loads(result.stdout)

        finally:
            os.unlink(input_file)

    def _generate_countermodel(
        self,
        proposition: str,
        world: str,
        accessible_worlds: List[str],
        valuations: Dict[str, bool]
    ) -> Dict[str, Any]:
        """
        Generate a countermodel (falsifying Kripke model) for a false proposition

        Uses systematic Kripke semantics to construct a model that makes the
        proposition false, providing traceable falsifiability evidence.

        Args:
            proposition: The false modal logic formula
            world: Current world identifier
            accessible_worlds: List of accessible world identifiers
            valuations: Current truth value assignments

        Returns:
            Dictionary containing countermodel specification and trace
        """
        logger.info(f"Generating countermodel for false proposition: {proposition}")

        # Extract atomic propositions from formula
        atomic_props = self._extract_atomic_propositions(proposition)

        # Generate systematic countermodel by exploring valuation space
        countermodel = {
            "falsifying_world": world,
            "kripke_structure": {
                "worlds": accessible_worlds,
                "accessibility_relation": self._generate_accessibility_relation(accessible_worlds),
                "valuation_function": {}
            },
            "falsification_trace": [],
            "proposition": proposition,
            "countermodel_type": "kripke_systematic"
        }

        # Try different valuations to find falsifying assignment
        for valuation_attempt in self._generate_valuation_space(atomic_props):
            try:
                test_result = self.evaluate_modal_proposition(
                    proposition, world, accessible_worlds, valuation_attempt,
                    generate_countermodel=False  # Avoid recursion
                )

                if test_result.get("success", False) and not test_result.get("result", True):
                    # Found falsifying valuation
                    countermodel["kripke_structure"]["valuation_function"] = valuation_attempt
                    countermodel["falsification_trace"].append({
                        "step": "falsifying_valuation_found",
                        "valuation": valuation_attempt,
                        "result": test_result.get("result"),
                        "world": world
                    })
                    break

            except Exception as e:
                countermodel["falsification_trace"].append({
                    "step": "valuation_test_error",
                    "valuation": valuation_attempt,
                    "error": str(e)
                })
                continue

        # Generate specific countermodel for modal operators
        if any(op in proposition for op in ["[]", "<>", "Box", "Diamond"]):
            modal_countermodel = self._generate_modal_countermodel(
                proposition, world, accessible_worlds, atomic_props
            )
            countermodel["modal_specific"] = modal_countermodel

        countermodel["falsification_trace"].append({
            "step": "countermodel_complete",
            "verification": "countermodel_generation_finished"
        })

        return countermodel

    def _extract_atomic_propositions(self, proposition: str) -> List[str]:
        """Extract atomic proposition names from modal formula"""
        import re

        # Remove modal operators and logical connectives
        cleaned = re.sub(r'(\[\]|<>|Box|Diamond|&&|\|\||->|~|\(|\))', ' ', proposition)

        # Extract potential atomic propositions (letters/words)
        atoms = re.findall(r'[a-zA-Z][a-zA-Z0-9_]*', cleaned)

        # Filter out keywords
        keywords = {'true', 'false', 'True', 'False', 'Box', 'Diamond'}
        atoms = [atom for atom in atoms if atom not in keywords]

        return list(set(atoms))  # Remove duplicates

    def _generate_accessibility_relation(self, worlds: List[str]) -> Dict[str, List[str]]:
        """Generate accessibility relation for Kripke model"""
        # Default: each world accessible to itself and others
        relation = {}
        for world in worlds:
            relation[world] = worlds.copy()  # Reflexive and complete
        return relation

    def _generate_valuation_space(self, atomic_props: List[str]) -> List[Dict[str, bool]]:
        """Generate all possible truth value assignments for atomic propositions"""
        if not atomic_props:
            return [{}]

        # Generate all 2^n combinations for n atomic propositions
        from itertools import product

        valuations = []
        for truth_values in product([True, False], repeat=len(atomic_props)):
            valuation = dict(zip(atomic_props, truth_values))
            valuations.append(valuation)

        return valuations

    def _generate_modal_countermodel(
        self,
        proposition: str,
        world: str,
        accessible_worlds: List[str],
        atomic_props: List[str]
    ) -> Dict[str, Any]:
        """Generate modal-specific countermodel for Box/Diamond operators"""
        modal_countermodel = {
            "type": "modal_operator_countermodel",
            "proposition": proposition,
            "strategy": "accessibility_manipulation"
        }

        # For Box (□) propositions: find world where inner formula is false
        if "[]" in proposition or "Box" in proposition:
            modal_countermodel["strategy"] = "box_falsification"
            modal_countermodel["technique"] = "find_accessible_world_where_inner_false"

            # Create specific world structure to falsify Box formula
            modal_countermodel["falsifying_structure"] = {
                "worlds": accessible_worlds + [f"counter_w{i}" for i in range(2)],
                "accessibility": {
                    world: accessible_worlds + [f"counter_w{i}" for i in range(2)]
                },
                "target_false_world": "counter_w0"
            }

        # For Diamond (◊) propositions: make all accessible worlds false for inner formula
        elif "<>" in proposition or "Diamond" in proposition:
            modal_countermodel["strategy"] = "diamond_falsification"
            modal_countermodel["technique"] = "make_all_accessible_worlds_false_for_inner"

            modal_countermodel["falsifying_structure"] = {
                "worlds": accessible_worlds,
                "accessibility": {world: accessible_worlds},
                "all_worlds_false_for_inner": True
            }

        return modal_countermodel

    def evaluate_batch(
        self,
        propositions: List[str],
        world: str = "w0",
        accessible_worlds: Optional[List[str]] = None,
        valuations: Optional[Dict[str, bool]] = None
    ) -> Dict[str, Any]:
        """
        Evaluate multiple modal propositions in batch

        Args:
            propositions: List of modal logic formulas
            world: Current world identifier
            accessible_worlds: List of accessible world identifiers
            valuations: Dictionary mapping atomic propositions to truth values

        Returns:
            Dictionary containing batch evaluation results
        """
        if accessible_worlds is None:
            accessible_worlds = [world]
        if valuations is None:
            valuations = {}

        results = []
        for prop in propositions:
            result = self.evaluate_modal_proposition(
                prop, world, accessible_worlds, valuations
            )
            results.append(result)

        return {
            "batch_results": results,
            "total_count": len(propositions),
            "success_count": sum(1 for r in results if r.get("success", False)),
            "context": {
                "world": world,
                "accessible_worlds": accessible_worlds,
                "valuations": valuations
            }
        }

    def validate_syntax(self, proposition: str) -> Dict[str, Any]:
        """
        Validate the syntax of a modal logic proposition without evaluation

        Args:
            proposition: Modal logic formula to validate

        Returns:
            Dictionary indicating if syntax is valid
        """
        try:
            # Attempt to parse without evaluation
            result = self.evaluate_modal_proposition(
                proposition,
                world="dummy",
                accessible_worlds=["dummy"],
                valuations={}
            )

            if "error" in result and "Parse error" in result["error"]:
                return {
                    "valid": False,
                    "error": result["error"],
                    "proposition": proposition
                }
            else:
                return {
                    "valid": True,
                    "proposition": proposition
                }
        except Exception as e:
            return {
                "valid": False,
                "error": str(e),
                "proposition": proposition
            }

class IELEvaluator(ModalLogicEvaluator):
    """
    Extended evaluator for Identity-Experiential Logic (IEL)

    Provides evaluation capabilities for IEL operators in addition to
    standard modal logic.
    """

    def evaluate_iel_proposition(
        self,
        iel_formula: str,
        world: str = "w0",
        accessible_worlds: Optional[List[str]] = None,
        valuations: Optional[Dict[str, bool]] = None,
        identity_context: Optional[Dict[str, Any]] = None,
        experience_context: Optional[Dict[str, Any]] = None,
        generate_countermodel: bool = True
    ) -> Dict[str, Any]:
        """
        Evaluate an IEL proposition with identity and experience operators

        Args:
            iel_formula: IEL formula with I() and E() operators
            world: Current world identifier
            accessible_worlds: List of accessible world identifiers
            valuations: Dictionary mapping atomic propositions to truth values
            identity_context: Context for identity operator evaluation
            experience_context: Context for experience operator evaluation
            generate_countermodel: Whether to generate countermodels for false propositions

        Returns:
            Dictionary containing IEL evaluation result and optional countermodel

        Example:
            >>> evaluator = IELEvaluator()
            >>> result = evaluator.evaluate_iel_proposition(
            ...     "I(agent1) && E(observation1) -> []goal",
            ...     identity_context={"agent1": "self"},
            ...     experience_context={"observation1": "sensory_data"}
            ... )
        """
        if accessible_worlds is None:
            accessible_worlds = [world]
        if valuations is None:
            valuations = {}
        if identity_context is None:
            identity_context = {}
        if experience_context is None:
            experience_context = {}

        # Transform IEL operators into modal logic propositions
        # This is a simplified transformation - full implementation would
        # require more sophisticated parsing and context handling
        transformed_formula = self._transform_iel_to_modal(
            iel_formula, identity_context, experience_context
        )

        # Evaluate using base modal logic evaluator
        result = self.evaluate_modal_proposition(
            transformed_formula, world, accessible_worlds, valuations,
            generate_countermodel=generate_countermodel
        )

        # Add IEL-specific metadata
        if result.get("success", False):
            result["iel_metadata"] = {
                "original_formula": iel_formula,
                "transformed_formula": transformed_formula,
                "identity_context": identity_context,
                "experience_context": experience_context
            }

            # Enhance countermodel with IEL-specific information
            if "countermodel" in result:
                result["countermodel"]["iel_specific"] = {
                    "original_iel_formula": iel_formula,
                    "identity_falsification": self._analyze_identity_falsification(
                        iel_formula, identity_context
                    ),
                    "experience_falsification": self._analyze_experience_falsification(
                        iel_formula, experience_context
                    ),
                    "transformation_trace": {
                        "original": iel_formula,
                        "transformed": transformed_formula,
                        "identity_mappings": identity_context,
                        "experience_mappings": experience_context
                    }
                }

        return result

    def _transform_iel_to_modal(
        self,
        iel_formula: str,
        identity_context: Dict[str, Any],
        experience_context: Dict[str, Any]
    ) -> str:
        """
        Transform IEL formula with I() and E() operators to pure modal logic

        This is a simplified transformation. A complete implementation would
        require proper parsing and semantic interpretation of IEL operators.
        """
        formula = iel_formula

        # Replace identity operators I(x) with propositions
        for identity, value in identity_context.items():
            formula = formula.replace(f"I({identity})", f"identity_{identity}")

        # Replace experience operators E(x) with modal propositions
        for experience, value in experience_context.items():
            formula = formula.replace(f"E({experience})", f"<>experience_{experience}")

        return formula

    def _analyze_identity_falsification(
        self,
        iel_formula: str,
        identity_context: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Analyze how identity operators contribute to formula falsification"""
        identity_analysis = {
            "identity_operators_found": [],
            "falsification_strategy": "identity_contradiction"
        }

        import re
        identity_matches = re.findall(r'I\(([^)]+)\)', iel_formula)

        for identity in identity_matches:
            identity_analysis["identity_operators_found"].append({
                "operator": f"I({identity})",
                "context_value": identity_context.get(identity, "undefined"),
                "falsification_method": "contradict_identity_binding"
            })

        return identity_analysis

    def _analyze_experience_falsification(
        self,
        iel_formula: str,
        experience_context: Dict[str, Any]
    ) -> Dict[str, Any]:
        """Analyze how experience operators contribute to formula falsification"""
        experience_analysis = {
            "experience_operators_found": [],
            "falsification_strategy": "experience_unavailability"
        }

        import re
        experience_matches = re.findall(r'E\(([^)]+)\)', iel_formula)

        for experience in experience_matches:
            experience_analysis["experience_operators_found"].append({
                "operator": f"E({experience})",
                "context_value": experience_context.get(experience, "undefined"),
                "falsification_method": "make_experience_inaccessible"
            })

        return experience_analysis

def create_evaluator(evaluator_type: str = "modal") -> Union[ModalLogicEvaluator, IELEvaluator]:
    """
    Factory function to create appropriate evaluator instance

    Args:
        evaluator_type: Type of evaluator ("modal" or "iel")

    Returns:
        Evaluator instance
    """
    if evaluator_type == "iel":
        return IELEvaluator()
    elif evaluator_type == "modal":
        return ModalLogicEvaluator()
    else:
        raise ValueError(f"Unknown evaluator type: {evaluator_type}")

# Runtime validation helper
def verify_bridge_consistency() -> bool:
    """
    Verify that the proof bridge is working correctly by running test cases

    Returns:
        True if bridge passes consistency checks
    """
    try:
        evaluator = ModalLogicEvaluator()

        # Test basic propositions
        test_cases = [
            ("p", {"p": True}, True),
            ("p", {"p": False}, False),
            ("p && q", {"p": True, "q": True}, True),
            ("p && q", {"p": True, "q": False}, False),
            ("p || q", {"p": False, "q": True}, True),
            ("~p", {"p": False}, True),
        ]

        for prop, vals, expected in test_cases:
            result = evaluator.evaluate_modal_proposition(
                prop, valuations=vals
            )
            if not result.get("success", False):
                logger.error(f"Bridge test failed for {prop}: {result}")
                return False
            if result["result"] != expected:
                logger.error(f"Bridge test wrong result for {prop}: got {result['result']}, expected {expected}")
                return False

        logger.info("Proof bridge consistency verification passed")
        return True

    except Exception as e:
        logger.error(f"Bridge consistency check failed: {e}")
        return False

if __name__ == "__main__":
    # Demo usage
    print("LOGOS AGI Proof Bridge - Modal Logic Evaluator")
    print("=" * 50)

    evaluator = ModalLogicEvaluator()

    # Test basic modal logic
    test_prop = "[]p -> p"
    result = evaluator.evaluate_modal_proposition(
        test_prop,
        world="w0",
        accessible_worlds=["w0", "w1"],
        valuations={"p": True}
    )

    print(f"Evaluating: {test_prop}")
    print(f"Result: {json.dumps(result, indent=2)}")

    # Test IEL evaluation
    iel_evaluator = IELEvaluator()
    iel_result = iel_evaluator.evaluate_iel_proposition(
        "I(self) && E(input) -> []action",
        identity_context={"self": "agent"},
        experience_context={"input": "sensory"}
    )

    print(f"\nIEL Evaluation Result: {json.dumps(iel_result, indent=2)}")

    # Verify consistency
    print(f"\nBridge Consistency Check: {verify_bridge_consistency()}")
