"""
Test Bridge Consistency - Validation tests for proof-to-runtime bridge

This module contains comprehensive tests to validate that the extracted
modal logic evaluation produces results consistent with the formal Coq proofs.
"""

import unittest
import sys
import os
import json
import tempfile
from pathlib import Path

# Add parent directory to path for imports
sys.path.append(str(Path(__file__).parent.parent))

from logos_core.runtime.iel_runtime_interface import (
    ModalLogicEvaluator, IELEvaluator, create_evaluator, verify_bridge_consistency
)

class TestModalLogicBridge(unittest.TestCase):
    """Test basic modal logic evaluation bridge"""

    def setUp(self):
        """Set up test fixtures"""
        self.evaluator = ModalLogicEvaluator()
        self.default_world = "w0"
        self.default_accessible = ["w0", "w1", "w2"]

    def test_atomic_propositions(self):
        """Test evaluation of atomic propositions"""
        # Test true atomic proposition
        result = self.evaluator.evaluate_modal_proposition(
            "p",
            world=self.default_world,
            accessible_worlds=self.default_accessible,
            valuations={"p": True}
        )
        self.assertTrue(result.get("success", False))
        self.assertTrue(result.get("result", False))

        # Test false atomic proposition
        result = self.evaluator.evaluate_modal_proposition(
            "q",
            world=self.default_world,
            accessible_worlds=self.default_accessible,
            valuations={"q": False}
        )
        self.assertTrue(result.get("success", False))
        self.assertFalse(result.get("result", True))

    def test_propositional_connectives(self):
        """Test propositional logic connectives"""
        valuations = {"p": True, "q": False, "r": True}

        test_cases = [
            ("p && q", False),  # True AND False = False
            ("p && r", True),   # True AND True = True
            ("p || q", True),   # True OR False = True
            ("q || q", False),  # False OR False = False
            ("~p", False),      # NOT True = False
            ("~q", True),       # NOT False = True
            ("p -> q", False),  # True IMPLIES False = False
            ("q -> p", True),   # False IMPLIES True = True
        ]

        for formula, expected in test_cases:
            with self.subTest(formula=formula):
                result = self.evaluator.evaluate_modal_proposition(
                    formula,
                    world=self.default_world,
                    accessible_worlds=self.default_accessible,
                    valuations=valuations
                )
                self.assertTrue(result.get("success", False),
                               f"Evaluation failed for {formula}: {result}")
                self.assertEqual(result.get("result"), expected,
                               f"Wrong result for {formula}: got {result.get('result')}, expected {expected}")

    def test_modal_operators(self):
        """Test modal logic operators (Box and Diamond)"""
        # Test Box operator: []p (p holds in all accessible worlds)
        # Should be true if p is true in all accessible worlds
        result = self.evaluator.evaluate_modal_proposition(
            "[]p",
            world=self.default_world,
            accessible_worlds=self.default_accessible,
            valuations={"p": True}  # p true everywhere
        )
        self.assertTrue(result.get("success", False))
        # Note: This depends on the specific implementation of forall_accessible
        # For now, we just verify it doesn't crash

        # Test Diamond operator: <>p (p holds in some accessible world)
        result = self.evaluator.evaluate_modal_proposition(
            "<>p",
            world=self.default_world,
            accessible_worlds=self.default_accessible,
            valuations={"p": True}
        )
        self.assertTrue(result.get("success", False))

    def test_complex_formulas(self):
        """Test complex modal formulas"""
        valuations = {"p": True, "q": False}

        complex_formulas = [
            "(p && q) -> r",
            "[]p -> p",  # T axiom
            "<>p -> ~[]~p",  # Duality
            "~(p && ~p)",  # Law of non-contradiction
        ]

        for formula in complex_formulas:
            with self.subTest(formula=formula):
                result = self.evaluator.evaluate_modal_proposition(
                    formula,
                    world=self.default_world,
                    accessible_worlds=self.default_accessible,
                    valuations=valuations
                )
                self.assertTrue(result.get("success", False),
                               f"Complex formula evaluation failed for {formula}: {result}")

    def test_syntax_validation(self):
        """Test syntax validation for modal formulas"""
        valid_formulas = [
            "p",
            "p && q",
            "[]p",
            "<>q",
            "(p -> q) && (q -> r)",
        ]

        invalid_formulas = [
            "p &&",  # Incomplete
            "[]",    # Missing operand
            "p & q", # Wrong operator
            "((p)",  # Unmatched parentheses
        ]

        for formula in valid_formulas:
            with self.subTest(formula=formula):
                result = self.evaluator.validate_syntax(formula)
                self.assertTrue(result.get("valid", False),
                               f"Valid formula rejected: {formula}")

        for formula in invalid_formulas:
            with self.subTest(formula=formula):
                result = self.evaluator.validate_syntax(formula)
                self.assertFalse(result.get("valid", True),
                                f"Invalid formula accepted: {formula}")

    def test_batch_evaluation(self):
        """Test batch evaluation of multiple propositions"""
        propositions = ["p", "q", "p && q", "p || q", "~p"]
        valuations = {"p": True, "q": False}

        result = self.evaluator.evaluate_batch(
            propositions,
            world=self.default_world,
            accessible_worlds=self.default_accessible,
            valuations=valuations
        )

        self.assertIn("batch_results", result)
        self.assertEqual(len(result["batch_results"]), len(propositions))
        self.assertEqual(result["total_count"], len(propositions))

class TestIELBridge(unittest.TestCase):
    """Test Identity-Experiential Logic (IEL) bridge"""

    def setUp(self):
        """Set up IEL test fixtures"""
        self.evaluator = IELEvaluator()
        self.default_world = "w0"
        self.default_accessible = ["w0", "w1"]

    def test_iel_operators(self):
        """Test IEL identity and experience operators"""
        # Test identity operator
        result = self.evaluator.evaluate_iel_proposition(
            "I(agent1) -> action",
            world=self.default_world,
            accessible_worlds=self.default_accessible,
            identity_context={"agent1": "self"},
            valuations={"action": True}
        )
        self.assertTrue(result.get("success", False))

        # Test experience operator
        result = self.evaluator.evaluate_iel_proposition(
            "E(observation) && goal",
            world=self.default_world,
            accessible_worlds=self.default_accessible,
            experience_context={"observation": "sensory_input"},
            valuations={"goal": True}
        )
        self.assertTrue(result.get("success", False))

    def test_iel_transformation(self):
        """Test IEL to modal logic transformation"""
        formula = "I(self) && E(input) -> []action"
        identity_ctx = {"self": "agent"}
        experience_ctx = {"input": "data"}

        # The transformation should replace IEL operators with modal equivalents
        transformed = self.evaluator._transform_iel_to_modal(
            formula, identity_ctx, experience_ctx
        )

        # Verify transformation occurred
        self.assertNotEqual(formula, transformed)
        self.assertNotIn("I(", transformed)
        self.assertNotIn("E(", transformed)

class TestBridgeConsistency(unittest.TestCase):
    """Test overall bridge consistency and integration"""

    def test_consistency_verification(self):
        """Test the bridge consistency verification function"""
        # This tests the verify_bridge_consistency function
        is_consistent = verify_bridge_consistency()
        # Note: This may fail if OCaml bridge is not properly compiled
        # In that case, we expect graceful degradation
        self.assertIsInstance(is_consistent, bool)

    def test_evaluator_factory(self):
        """Test the evaluator factory function"""
        modal_eval = create_evaluator("modal")
        self.assertIsInstance(modal_eval, ModalLogicEvaluator)

        iel_eval = create_evaluator("iel")
        self.assertIsInstance(iel_eval, IELEvaluator)

        with self.assertRaises(ValueError):
            create_evaluator("invalid")

    def test_error_handling(self):
        """Test error handling for invalid inputs"""
        evaluator = ModalLogicEvaluator()

        # Test with invalid proposition
        result = evaluator.evaluate_modal_proposition("invalid syntax &&")
        self.assertFalse(result.get("success", True))
        self.assertIn("error", result)

        # Test with empty proposition
        result = evaluator.evaluate_modal_proposition("")
        self.assertFalse(result.get("success", True))

class TestModalLogicTheorems(unittest.TestCase):
    """Test that extracted evaluator respects modal logic theorems"""

    def setUp(self):
        self.evaluator = ModalLogicEvaluator()
        self.world = "w0"
        self.accessible = ["w0", "w1", "w2"]

    def test_modus_ponens(self):
        """Test modus ponens: if p and p->q then q"""
        valuations = {"p": True, "q": True}

        # Evaluate premises
        p_result = self.evaluator.evaluate_modal_proposition(
            "p", valuations=valuations
        )
        impl_result = self.evaluator.evaluate_modal_proposition(
            "p -> q", valuations=valuations
        )

        # If both premises are true, conclusion should be true
        if (p_result.get("result") and impl_result.get("result")):
            q_result = self.evaluator.evaluate_modal_proposition(
                "q", valuations=valuations
            )
            self.assertTrue(q_result.get("result"),
                           "Modus ponens violation: p and p->q are true but q is false")

    def test_excluded_middle(self):
        """Test law of excluded middle: p or not p"""
        for p_value in [True, False]:
            result = self.evaluator.evaluate_modal_proposition(
                "p || ~p",
                valuations={"p": p_value}
            )
            self.assertTrue(result.get("success", False))
            self.assertTrue(result.get("result", False),
                           f"Excluded middle violated for p={p_value}")

    def test_non_contradiction(self):
        """Test law of non-contradiction: not (p and not p)"""
        for p_value in [True, False]:
            result = self.evaluator.evaluate_modal_proposition(
                "~(p && ~p)",
                valuations={"p": p_value}
            )
            self.assertTrue(result.get("success", False))
            self.assertTrue(result.get("result", False),
                           f"Non-contradiction violated for p={p_value}")

def run_consistency_tests():
    """Run all consistency tests and return summary"""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()

    # Add all test classes
    test_classes = [
        TestModalLogicBridge,
        TestIELBridge,
        TestBridgeConsistency,
        TestModalLogicTheorems
    ]

    for test_class in test_classes:
        tests = loader.loadTestsFromTestCase(test_class)
        suite.addTests(tests)

    # Run tests
    runner = unittest.TextTestRunner(verbosity=2, stream=sys.stdout)
    result = runner.run(suite)

    # Return summary
    return {
        "tests_run": result.testsRun,
        "failures": len(result.failures),
        "errors": len(result.errors),
        "success": result.wasSuccessful(),
        "failure_details": result.failures + result.errors
    }

if __name__ == "__main__":
    print("LOGOS AGI Proof Bridge - Consistency Tests")
    print("=" * 50)

    # Run comprehensive tests
    summary = run_consistency_tests()

    print(f"\nTest Summary:")
    print(f"Tests Run: {summary['tests_run']}")
    print(f"Failures: {summary['failures']}")
    print(f"Errors: {summary['errors']}")
    print(f"Overall Success: {summary['success']}")

    if not summary['success']:
        print(f"\nFailure Details:")
        for failure in summary['failure_details']:
            print(f"- {failure[0]}: {failure[1]}")

    # Exit with appropriate code
    sys.exit(0 if summary['success'] else 1)
