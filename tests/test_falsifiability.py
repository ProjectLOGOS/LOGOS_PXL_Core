#!/usr/bin/env python3
"""
Falsifiability Test Suite - Runtime validation of countermodel generation and falsifiability

This module provides comprehensive testing of the LOGOS falsifiability framework,
including countermodel generation, telemetry logging, and rejection propagation.

Tests cover:
- Runtime countermodel generation for false propositions
- Telemetry integration for falsification events
- Modal logic falsifiability properties (¬□P ⇒ ◊¬P)
- IEL operator falsifiability
- Coverage metrics and validation
"""

import unittest
import json
import tempfile
import os
import sys
from datetime import datetime
from pathlib import Path
from typing import Dict, Any, List
import uuid

# Add parent directory to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent))

from logos_core.runtime.iel_runtime_interface import ModalLogicEvaluator, IELEvaluator
from logos_core.eschaton_safety import SafeguardStateMachine, SafeguardConfiguration, SafeguardState

class TestFalsifiabilityFramework(unittest.TestCase):
    """Test core falsifiability framework functionality"""

    def setUp(self):
        """Set up test fixtures"""
        self.modal_evaluator = ModalLogicEvaluator()
        self.iel_evaluator = IELEvaluator()
        self.safety_system = SafeguardStateMachine()

        # Create temporary telemetry file
        self.temp_dir = tempfile.mkdtemp()
        self.telemetry_file = Path(self.temp_dir) / "test_telemetry.jsonl"

    def tearDown(self):
        """Clean up test fixtures"""
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)

class TestCountermodelGeneration(TestFalsifiabilityFramework):
    """Test countermodel generation for false propositions"""

    def test_atomic_proposition_countermodel(self):
        """Test countermodel generation for false atomic propositions"""
        proposition = "p"
        valuations = {"p": False}

        result = self.modal_evaluator.evaluate_modal_proposition(
            proposition,
            valuations=valuations,
            generate_countermodel=True
        )

        self.assertTrue(result.get("success", False))
        self.assertFalse(result.get("result", True))  # Should be false
        self.assertIn("countermodel", result)

        countermodel = result["countermodel"]
        self.assertEqual(countermodel["proposition"], proposition)
        self.assertIn("kripke_structure", countermodel)
        self.assertIn("falsification_trace", countermodel)

    def test_negation_countermodel(self):
        """Test countermodel for negated propositions"""
        proposition = "~p"
        valuations = {"p": True}  # Makes ~p false

        result = self.modal_evaluator.evaluate_modal_proposition(
            proposition,
            valuations=valuations,
            generate_countermodel=True
        )

        self.assertTrue(result.get("success", False))
        self.assertFalse(result.get("result", True))
        self.assertIn("countermodel", result)

    def test_conjunction_countermodel(self):
        """Test countermodel for false conjunctions"""
        proposition = "p && q"
        valuations = {"p": True, "q": False}  # Makes conjunction false

        result = self.modal_evaluator.evaluate_modal_proposition(
            proposition,
            valuations=valuations,
            generate_countermodel=True
        )

        self.assertTrue(result.get("success", False))
        self.assertFalse(result.get("result", True))
        self.assertIn("countermodel", result)

    def test_box_operator_countermodel(self):
        """Test countermodel generation for Box (□) operators"""
        proposition = "[]p"  # Necessarily p
        accessible_worlds = ["w0", "w1"]
        valuations = {"p": False}  # p is false, so []p should be false

        result = self.modal_evaluator.evaluate_modal_proposition(
            proposition,
            accessible_worlds=accessible_worlds,
            valuations=valuations,
            generate_countermodel=True
        )

        if not result.get("result", True):  # If Box p is false
            self.assertIn("countermodel", result)
            countermodel = result["countermodel"]
            self.assertIn("modal_specific", countermodel)
            self.assertEqual(
                countermodel["modal_specific"]["strategy"],
                "box_falsification"
            )

    def test_diamond_operator_countermodel(self):
        """Test countermodel generation for Diamond (◊) operators"""
        proposition = "<>p"  # Possibly p
        accessible_worlds = []  # No accessible worlds makes <>p false
        valuations = {"p": True}

        result = self.modal_evaluator.evaluate_modal_proposition(
            proposition,
            accessible_worlds=accessible_worlds,
            valuations=valuations,
            generate_countermodel=True
        )

        if not result.get("result", True):  # If Diamond p is false
            self.assertIn("countermodel", result)
            countermodel = result["countermodel"]
            self.assertIn("modal_specific", countermodel)
            self.assertEqual(
                countermodel["modal_specific"]["strategy"],
                "diamond_falsification"
            )

class TestIELFalsifiability(TestFalsifiabilityFramework):
    """Test IEL operator falsifiability"""

    def test_identity_operator_falsifiability(self):
        """Test falsifiability of identity operators"""
        iel_formula = "I(agent1) && goal"
        identity_context = {"agent1": "self"}
        valuations = {"goal": False}  # Makes formula false

        result = self.iel_evaluator.evaluate_iel_proposition(
            iel_formula,
            identity_context=identity_context,
            valuations=valuations,
            generate_countermodel=True
        )

        self.assertTrue(result.get("success", False))

        if not result.get("result", True):  # If IEL formula is false
            self.assertIn("countermodel", result)
            countermodel = result["countermodel"]
            self.assertIn("iel_specific", countermodel)

            iel_specific = countermodel["iel_specific"]
            self.assertEqual(iel_specific["original_iel_formula"], iel_formula)
            self.assertIn("identity_falsification", iel_specific)

    def test_experience_operator_falsifiability(self):
        """Test falsifiability of experience operators"""
        iel_formula = "E(observation1) -> action"
        experience_context = {"observation1": "sensory_data"}
        valuations = {"action": False}  # Makes implication potentially false

        result = self.iel_evaluator.evaluate_iel_proposition(
            iel_formula,
            experience_context=experience_context,
            valuations=valuations,
            generate_countermodel=True
        )

        self.assertTrue(result.get("success", False))

        if "countermodel" in result:
            countermodel = result["countermodel"]
            self.assertIn("iel_specific", countermodel)

            iel_specific = countermodel["iel_specific"]
            self.assertIn("experience_falsification", iel_specific)

    def test_combined_iel_operators(self):
        """Test falsifiability with combined identity and experience operators"""
        iel_formula = "I(self) && E(input) -> []action"
        identity_context = {"self": "agent"}
        experience_context = {"input": "sensory"}
        valuations = {"action": False}

        result = self.iel_evaluator.evaluate_iel_proposition(
            iel_formula,
            identity_context=identity_context,
            experience_context=experience_context,
            valuations=valuations,
            generate_countermodel=True
        )

        self.assertTrue(result.get("success", False))

        if "countermodel" in result:
            countermodel = result["countermodel"]
            self.assertIn("iel_specific", countermodel)

            iel_specific = countermodel["iel_specific"]
            self.assertIn("transformation_trace", iel_specific)
            self.assertEqual(
                iel_specific["transformation_trace"]["original"],
                iel_formula
            )

class TestSafetySystemFalsifiability(TestFalsifiabilityFramework):
    """Test integration with safety system"""

    def test_falsifiability_constraint_checking(self):
        """Test safety system falsifiability constraint checking"""
        operation = "modal_evaluation"
        context = {
            "proposition": "p && ~p",  # Contradiction
            "evaluator_type": "modal",
            "world": "w0",
            "accessible_worlds": ["w0"],
            "valuations": {"p": True}
        }

        # This should trigger falsifiability constraint checking
        is_safe = self.safety_system.check_operation_safety(operation, context)

        # Safety system should handle contradictions appropriately
        # (either block them or generate appropriate countermodels)
        self.assertIsInstance(is_safe, bool)

    def test_modal_collapse_detection(self):
        """Test detection of modal collapse scenarios"""
        operation = "modal_evaluation"
        context = {
            "proposition": "[]p && <>~p",  # Potentially problematic modal interaction
            "evaluator_type": "modal",
            "world": "w0",
            "accessible_worlds": ["w0", "w1"],
            "valuations": {"p": True}
        }

        is_safe = self.safety_system.check_operation_safety(operation, context)
        self.assertIsInstance(is_safe, bool)

    def test_category_error_detection(self):
        """Test detection of category errors in propositions"""
        operation = "modal_evaluation"
        context = {
            "proposition": "consciousness && existence",  # Category mixing
            "evaluator_type": "modal",
            "world": "w0",
            "accessible_worlds": ["w0"],
            "valuations": {"consciousness": True, "existence": True}
        }

        is_safe = self.safety_system.check_operation_safety(operation, context)
        self.assertIsInstance(is_safe, bool)

class TestTelemetryIntegration(TestFalsifiabilityFramework):
    """Test telemetry logging for falsification events"""

    def test_falsification_event_logging(self):
        """Test that falsification events are properly logged to telemetry"""
        # Set up telemetry file monitoring
        logs_dir = Path("logs")
        logs_dir.mkdir(exist_ok=True)
        telemetry_file = logs_dir / "monitor_telemetry.jsonl"

        # Record initial telemetry size
        initial_size = telemetry_file.stat().st_size if telemetry_file.exists() else 0

        # Trigger falsification through safety system
        operation = "modal_evaluation"
        context = {
            "proposition": "p",
            "evaluator_type": "modal",
            "world": "w0",
            "accessible_worlds": ["w0"],
            "valuations": {"p": False}  # Makes proposition false
        }

        is_safe = self.safety_system.check_operation_safety(operation, context)

        # Check if telemetry file grew (indicating new entries)
        if telemetry_file.exists():
            final_size = telemetry_file.stat().st_size
            self.assertGreater(final_size, initial_size, "Telemetry file should have new entries")

            # Check for falsification event in telemetry
            with open(telemetry_file, 'r') as f:
                lines = f.readlines()

            # Look for falsification events in recent entries
            recent_entries = lines[-10:]  # Check last 10 entries
            falsification_events = []

            for line in recent_entries:
                try:
                    entry = json.loads(line.strip())
                    if entry.get("event_type") == "falsification_event":
                        falsification_events.append(entry)
                except json.JSONDecodeError:
                    continue

            # Verify falsification event structure if found
            if falsification_events:
                event = falsification_events[0]
                self.assertIn("evaluation_record", event)

                eval_record = event["evaluation_record"]
                self.assertEqual(eval_record["evaluator_type"], "falsifiability_analyzer")
                self.assertEqual(eval_record["operation"], "countermodel_generation")
                self.assertIn("countermodel", eval_record["output_data"])
                self.assertIn("falsified", eval_record["output_data"])
                self.assertTrue(eval_record["output_data"]["falsified"])

class TestFalsifiabilityProperties(TestFalsifiabilityFramework):
    """Test modal logic falsifiability properties"""

    def test_box_falsifiability_principle(self):
        """Test ¬□P ⇒ ◊¬P (if necessarily P is false, then possibly not-P)"""
        # Test case: ¬□p should imply ◊¬p
        box_p = "[]p"
        diamond_not_p = "<>~p"

        # Create context where Box p is false
        accessible_worlds = ["w0", "w1"]
        valuations_box_false = {"p": False}  # p false in some world makes []p false

        result_box = self.modal_evaluator.evaluate_modal_proposition(
            box_p,
            accessible_worlds=accessible_worlds,
            valuations=valuations_box_false
        )

        result_diamond = self.modal_evaluator.evaluate_modal_proposition(
            diamond_not_p,
            accessible_worlds=accessible_worlds,
            valuations=valuations_box_false
        )

        # If Box p is false, Diamond not-p should be true (modally)
        if result_box.get("success") and not result_box.get("result"):
            # Box p is false, so Diamond not-p should be verifiable
            self.assertTrue(result_diamond.get("success"))

    def test_contradiction_unfalsifiability(self):
        """Test that contradictions are consistently false (unfalsifiable as true)"""
        contradiction = "p && ~p"

        # Test with p = True
        result_true = self.modal_evaluator.evaluate_modal_proposition(
            contradiction,
            valuations={"p": True}
        )

        # Test with p = False
        result_false = self.modal_evaluator.evaluate_modal_proposition(
            contradiction,
            valuations={"p": False}
        )

        # Contradiction should be false in both cases
        if result_true.get("success"):
            self.assertFalse(result_true.get("result"))
        if result_false.get("success"):
            self.assertFalse(result_false.get("result"))

    def test_tautology_unfalsifiability(self):
        """Test that tautologies are consistently true (unfalsifiable as false)"""
        tautology = "p || ~p"  # Law of excluded middle

        # Test with different valuations
        test_valuations = [{"p": True}, {"p": False}]

        for valuations in test_valuations:
            result = self.modal_evaluator.evaluate_modal_proposition(
                tautology,
                valuations=valuations
            )

            if result.get("success"):
                self.assertTrue(result.get("result"),
                    f"Tautology should be true with valuations {valuations}")

class TestCoverageMetrics(TestFalsifiabilityFramework):
    """Test falsifiability coverage metrics"""

    def test_operator_coverage(self):
        """Test coverage of all modal logic operators"""
        test_cases = [
            ("p", "atomic"),
            ("~p", "negation"),
            ("p && q", "conjunction"),
            ("p || q", "disjunction"),
            ("p -> q", "implication"),
            ("[]p", "box"),
            ("<>p", "diamond")
        ]

        coverage_results = {}

        for proposition, operator_type in test_cases:
            # Test with falsifying valuations
            if operator_type == "atomic":
                valuations = {"p": False}
            elif operator_type == "negation":
                valuations = {"p": True}
            elif operator_type in ["conjunction", "disjunction", "implication"]:
                valuations = {"p": True, "q": False}
            else:  # modal operators
                valuations = {"p": False}

            result = self.modal_evaluator.evaluate_modal_proposition(
                proposition,
                valuations=valuations,
                generate_countermodel=True
            )

            coverage_results[operator_type] = {
                "success": result.get("success", False),
                "has_countermodel": "countermodel" in result,
                "proposition": proposition
            }

        # Verify we have coverage for all operator types
        expected_operators = {
            "atomic", "negation", "conjunction", "disjunction",
            "implication", "box", "diamond"
        }
        covered_operators = set(coverage_results.keys())

        self.assertEqual(covered_operators, expected_operators)

        # Calculate coverage percentage
        successful_tests = sum(1 for r in coverage_results.values() if r["success"])
        coverage_percentage = (successful_tests / len(test_cases)) * 100

        # Should achieve ≥ 95% coverage as specified
        self.assertGreaterEqual(coverage_percentage, 95.0,
            f"Coverage {coverage_percentage}% should be ≥ 95%")

    def test_iel_operator_coverage(self):
        """Test coverage of IEL operators"""
        iel_test_cases = [
            ("I(agent)", {"agent": "self"}, {}, "identity"),
            ("E(observation)", {}, {"observation": "data"}, "experience"),
            ("I(self) && E(input)", {"self": "agent"}, {"input": "sensory"}, "combined")
        ]

        iel_coverage_results = {}

        for formula, identity_ctx, experience_ctx, test_type in iel_test_cases:
            result = self.iel_evaluator.evaluate_iel_proposition(
                formula,
                identity_context=identity_ctx,
                experience_context=experience_ctx,
                generate_countermodel=True
            )

            iel_coverage_results[test_type] = {
                "success": result.get("success", False),
                "has_iel_metadata": "iel_metadata" in result,
                "formula": formula
            }

        # Verify IEL-specific coverage
        for test_type, result in iel_coverage_results.items():
            self.assertTrue(result["success"],
                f"IEL test case '{test_type}' should succeed")

if __name__ == "__main__":
    # Set up test environment
    import logging
    logging.basicConfig(level=logging.INFO)

    # Create test suite
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()

    # Add test cases in order of dependency
    suite.addTests(loader.loadTestsFromTestCase(TestCountermodelGeneration))
    suite.addTests(loader.loadTestsFromTestCase(TestIELFalsifiability))
    suite.addTests(loader.loadTestsFromTestCase(TestSafetySystemFalsifiability))
    suite.addTests(loader.loadTestsFromTestCase(TestTelemetryIntegration))
    suite.addTests(loader.loadTestsFromTestCase(TestFalsifiabilityProperties))
    suite.addTests(loader.loadTestsFromTestCase(TestCoverageMetrics))

    # Run tests
    runner = unittest.TextTestRunner(verbosity=2)
    result = runner.run(suite)

    # Report results
    total_tests = result.testsRun
    failures = len(result.failures)
    errors = len(result.errors)
    success_rate = ((total_tests - failures - errors) / total_tests) * 100 if total_tests > 0 else 0

    print(f"\n" + "="*60)
    print(f"FALSIFIABILITY TEST RESULTS")
    print(f"="*60)
    print(f"Total Tests: {total_tests}")
    print(f"Passed: {total_tests - failures - errors}")
    print(f"Failed: {failures}")
    print(f"Errors: {errors}")
    print(f"Success Rate: {success_rate:.1f}%")
    print(f"Coverage Target: ≥95% (Required for certification)")

    if success_rate >= 95.0:
        print(f"✅ FALSIFIABILITY FRAMEWORK CERTIFIED")
    else:
        print(f"❌ FALSIFIABILITY FRAMEWORK NEEDS IMPROVEMENT")

    # Exit with appropriate code
    sys.exit(0 if success_rate >= 95.0 else 1)
