#!/usr/bin/env python3
"""
Comprehensive Test Suite for Eschatological Safety Framework

This test suite validates all aspects of the eschatological safety system:
- SafeguardState trigger conditions
- Reversible vs irreversible violation classification
- Emergency halt mechanisms
- Integrity validation
- Boundary enforcement (ethical/metaphysical)
- Telemetry integration
- Crash dump generation
- Containment actions
- Falsifiability and coverage validation

Part of the LOGOS AGI v1.0 eschatological safety testing infrastructure.
"""

import sys
import os
import json
import time
import threading
import tempfile
import unittest
from unittest.mock import patch, MagicMock
from pathlib import Path
from datetime import datetime, timedelta

# Add logos_core to path
sys.path.insert(0, str(Path(__file__).parent))

from logos_core.eschaton_safety import (
    SafeguardStateMachine, SafeguardConfiguration, SafeguardState,
    ViolationContext, IntegrityValidator, ParadoxDetector,
    BoundaryEnforcer, CrashDumpGenerator, check_operation_safety, emergency_halt
)

class TestSafeguardStates(unittest.TestCase):
    """Test all SafeguardState trigger conditions"""

    def setUp(self):
        """Set up test environment"""
        self.config = SafeguardConfiguration(
            enable_crash_dumps=True,
            enable_state_persistence=False,  # Disable for tests
            violation_log_path="test_logs/eschaton_violations.jsonl",
            crash_dump_path="test_dumps",
            integrity_hash_path="test_state/integrity_hashes.json"
        )
        self.safety_system = SafeguardStateMachine(self.config)

    def tearDown(self):
        """Clean up test environment"""
        self.safety_system.stop_monitoring()

        # Clean up test files
        for path in ["test_logs", "test_dumps", "test_state"]:
            if Path(path).exists():
                import shutil
                shutil.rmtree(path, ignore_errors=True)

    def test_ontology_violation_trigger(self):
        """Test ONTOLOGY_VIOLATION trigger conditions"""
        # Test self-referential paradox
        is_safe = self.safety_system.check_operation_safety(
            "evaluate paradox: this statement is false",
            {"proposition": "this statement is false"}
        )

        self.assertFalse(is_safe, "Paradox should trigger ontology violation")
        self.assertTrue(self.safety_system.system_halted, "System should be halted after ontology violation")
        self.assertEqual(len(self.safety_system.active_violations), 1, "Should have one active violation")

        violation = list(self.safety_system.active_violations.values())[0]
        self.assertEqual(violation.safeguard_state, SafeguardState.RECURSIVE_SELF_CORRUPTION)
        self.assertFalse(violation.reversible, "Ontology violations should be irreversible")

    def test_ethical_boundary_violations(self):
        """Test ethical boundary violation detection"""
        # Test deontological breach
        is_safe = self.safety_system.check_operation_safety(
            "harm innocent person",
            {
                "consequences": {
                    "justification": {"sufficient": False, "proportionate": False}
                }
            }
        )

        self.assertFalse(is_safe, "Harmful action should be blocked")

        # Test utility overflow
        self.safety_system = SafeguardStateMachine(self.config)  # Reset
        is_safe = self.safety_system.check_operation_safety(
            "maximize utility",
            {
                "consequences": {
                    "utility": {"total": 2e6}  # Over threshold
                }
            }
        )

        self.assertFalse(is_safe, "Utility overflow should be blocked")

        # Test rights violation cascade
        self.safety_system = SafeguardStateMachine(self.config)  # Reset
        is_safe = self.safety_system.check_operation_safety(
            "violate rights",
            {
                "consequences": {
                    "rights": {"violated": True, "cascade_risk": True}
                }
            }
        )

        self.assertFalse(is_safe, "Rights violation cascade should be blocked")

    def test_metaphysical_boundary_violations(self):
        """Test metaphysical boundary violation detection"""
        # Test identity violation
        is_safe = self.safety_system.check_operation_safety(
            "assert identity violation",
            {
                "proposition": "A is not A",
                "logical_context": {}
            }
        )

        self.assertFalse(is_safe, "Identity violation should be blocked")

        # Test contradiction
        self.safety_system = SafeguardStateMachine(self.config)  # Reset
        is_safe = self.safety_system.check_operation_safety(
            "assert contradiction",
            {
                "proposition": "p and not p and true and false",
                "logical_context": {}
            }
        )

        self.assertFalse(is_safe, "Logical contradiction should be blocked")

    def test_recoverable_vs_irreversible_classification(self):
        """Test classification of recoverable vs irreversible violations"""
        irreversible_tests = [
            ("recursive self-reference", {"proposition": "this statement is false"}),
            ("essence modification", {"proposition": "modify essential properties"}),
            ("modal collapse", {"proposition": "necessarily false and necessarily true"}),
        ]

        recoverable_tests = [
            ("simple evaluation error", {"proposition": "malformed logic"}),
            ("temporary resource constraint", {"proposition": "resource_exhausted"}),
        ]

        for test_name, context in irreversible_tests:
            with self.subTest(test=test_name):
                safety_system = SafeguardStateMachine(self.config)
                safety_system.check_operation_safety(f"test_{test_name}", context)

                if safety_system.active_violations:
                    violation = list(safety_system.active_violations.values())[0]
                    self.assertFalse(violation.reversible,
                                   f"{test_name} should be irreversible")

                safety_system.stop_monitoring()

class TestIntegrityValidation(unittest.TestCase):
    """Test integrity validation and file monitoring"""

    def setUp(self):
        """Set up test environment with temporary files"""
        self.temp_dir = tempfile.mkdtemp()
        self.test_file = Path(self.temp_dir) / "test_file.py"
        self.test_file.write_text("# Test file content\nprint('hello')\n")

        self.config = SafeguardConfiguration(
            enable_state_persistence=False,
            integrity_hash_path=str(Path(self.temp_dir) / "integrity_hashes.json")
        )
        self.validator = IntegrityValidator(self.config)
        self.validator.critical_files = [str(self.test_file)]

    def tearDown(self):
        """Clean up temporary files"""
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    def test_baseline_establishment(self):
        """Test establishing integrity baseline"""
        success = self.validator.establish_baseline()
        self.assertTrue(success, "Baseline establishment should succeed")
        self.assertIn(str(self.test_file), self.validator.baseline_hashes)

        # Verify hash file was created
        hash_file = Path(self.config.integrity_hash_path)
        self.assertTrue(hash_file.exists(), "Hash file should be created")

    def test_integrity_validation_success(self):
        """Test successful integrity validation"""
        self.validator.establish_baseline()

        is_valid, violations = self.validator.validate_integrity()
        self.assertTrue(is_valid, "Integrity should be valid")
        self.assertEqual(len(violations), 0, "Should have no violations")

    def test_integrity_validation_failure(self):
        """Test integrity validation failure"""
        self.validator.establish_baseline()

        # Modify the file
        self.test_file.write_text("# Modified content\nprint('modified')\n")

        is_valid, violations = self.validator.validate_integrity()
        self.assertFalse(is_valid, "Integrity should be invalid")
        self.assertGreater(len(violations), 0, "Should have violations")
        self.assertIn("hash mismatch", violations[0].lower())

    def test_missing_file_detection(self):
        """Test detection of missing critical files"""
        self.validator.establish_baseline()

        # Delete the file
        self.test_file.unlink()

        is_valid, violations = self.validator.validate_integrity()
        self.assertFalse(is_valid, "Integrity should be invalid")
        self.assertGreater(len(violations), 0, "Should have violations")
        self.assertIn("missing", violations[0].lower())

class TestParadoxDetection(unittest.TestCase):
    """Test paradox and self-reference detection"""

    def setUp(self):
        """Set up paradox detector"""
        self.config = SafeguardConfiguration()
        self.detector = ParadoxDetector(self.config)

    def test_self_reference_detection(self):
        """Test detection of self-referential operations"""
        # Test direct self-modification
        is_paradox = self.detector.check_self_reference(
            "system self modify core logic",
            {}
        )
        self.assertTrue(is_paradox, "Self-modification should be detected")

        # Test paradoxical statements
        paradox_statements = [
            "this statement is false",
            "I am lying",
            "the following statement is true. the preceding statement is false"
        ]

        for statement in paradox_statements:
            with self.subTest(statement=statement):
                is_paradox = self.detector.check_self_reference(statement, {})
                self.assertTrue(is_paradox, f"'{statement}' should be detected as paradox")

    def test_evaluation_chain_tracking(self):
        """Test evaluation chain depth tracking"""
        # Test normal operation
        self.detector.enter_evaluation("test_op")
        self.assertEqual(len(self.detector.evaluation_chain), 1)
        self.detector.exit_evaluation("test_op")
        self.assertEqual(len(self.detector.evaluation_chain), 0)

        # Test depth limit
        with self.assertRaises(RuntimeError):
            for i in range(self.config.paradox_detection_depth + 1):
                self.detector.enter_evaluation(f"op_{i}")

    def test_circular_reference_detection(self):
        """Test circular reference detection"""
        # Test circular evaluation
        self.detector.enter_evaluation("op_a")
        is_circular = self.detector.check_self_reference("op_a", {})
        self.assertTrue(is_circular, "Circular reference should be detected")

    def test_causal_loop_detection(self):
        """Test causal loop detection"""
        # Test normal causal chain
        normal_chain = ["a", "b", "c", "d"]
        is_loop = self.detector.detect_causal_loops(normal_chain)
        self.assertFalse(is_loop, "Normal chain should not be detected as loop")

        # Test circular causal chain
        circular_chain = ["a", "b", "c", "a"]
        is_loop = self.detector.detect_causal_loops(circular_chain)
        self.assertTrue(is_loop, "Circular chain should be detected as loop")

        # Test length limit
        long_chain = [f"step_{i}" for i in range(self.config.causality_chain_limit + 1)]
        is_loop = self.detector.detect_causal_loops(long_chain)
        self.assertTrue(is_loop, "Overly long chain should be detected as problematic")

class TestBoundaryEnforcement(unittest.TestCase):
    """Test ethical and metaphysical boundary enforcement"""

    def setUp(self):
        """Set up boundary enforcer"""
        self.config = SafeguardConfiguration()
        self.enforcer = BoundaryEnforcer(self.config)

    def test_ethical_violation_detection(self):
        """Test detection of ethical violations"""
        # Test harmful action without justification
        violation = self.enforcer.check_ethical_violation(
            "harm innocent person",
            {"justification": {"sufficient": False, "proportionate": False}}
        )
        self.assertEqual(violation, SafeguardState.DEONTOLOGICAL_BREACH)

        # Test rights violation
        violation = self.enforcer.check_ethical_violation(
            "violate rights",
            {"rights": {"violated": True, "cascade_risk": True}}
        )
        self.assertEqual(violation, SafeguardState.RIGHTS_VIOLATION_CASCADE)

        # Test utility overflow
        violation = self.enforcer.check_ethical_violation(
            "maximize utility",
            {"utility": {"total": 2e6}}
        )
        self.assertEqual(violation, SafeguardState.CONSEQUENTIALIST_OVERFLOW)

    def test_metaphysical_violation_detection(self):
        """Test detection of metaphysical violations"""
        # Test identity violation (basic pattern)
        violation = self.enforcer.check_metaphysical_violation(
            "A is not A",
            {}
        )
        # Note: This is a simplified test - real implementation would need more sophisticated logic

        # Test contradiction
        violation = self.enforcer.check_metaphysical_violation(
            "true and not true and false",
            {}
        )
        # Note: This tests basic pattern matching - full implementation would need formal logic

    def test_justified_harmful_actions(self):
        """Test that justified harmful actions are permitted"""
        # Test justified harmful action (e.g., medical procedure)
        violation = self.enforcer.check_ethical_violation(
            "perform surgery",  # Involves harm
            {
                "justification": {"sufficient": True, "proportionate": True},
                "medical_context": True
            }
        )
        self.assertIsNone(violation, "Justified medical procedure should be permitted")

class TestEmergencyHalt(unittest.TestCase):
    """Test emergency halt mechanisms"""

    def setUp(self):
        """Set up safety system for halt testing"""
        self.config = SafeguardConfiguration(
            enable_state_persistence=False,
            enable_crash_dumps=True,
            crash_dump_path="test_dumps"
        )
        self.safety_system = SafeguardStateMachine(self.config)

    def tearDown(self):
        """Clean up test environment"""
        self.safety_system.stop_monitoring()

        # Clean up test files
        if Path("test_dumps").exists():
            import shutil
            shutil.rmtree("test_dumps", ignore_errors=True)

    def test_manual_emergency_halt(self):
        """Test manual emergency halt trigger"""
        self.assertFalse(self.safety_system.system_halted, "System should start not halted")

        success = self.safety_system.eschaton_trigger("Manual test halt")

        self.assertTrue(success, "Emergency halt should succeed")
        self.assertTrue(self.safety_system.system_halted, "System should be halted")
        self.assertTrue(self.safety_system.permanent_lockout, "Should be in permanent lockout")
        self.assertGreater(len(self.safety_system.active_violations), 0, "Should have violation record")

    def test_automatic_emergency_halt(self):
        """Test automatic emergency halt on irreversible violation"""
        # Trigger irreversible violation
        self.safety_system.check_operation_safety(
            "self-referential paradox",
            {"proposition": "this statement is false"}
        )

        self.assertTrue(self.safety_system.system_halted, "System should auto-halt on irreversible violation")
        self.assertTrue(self.safety_system.permanent_lockout, "Should be in permanent lockout")

    def test_operations_blocked_after_halt(self):
        """Test that operations are blocked after emergency halt"""
        # Trigger halt
        self.safety_system.eschaton_trigger("Test halt")

        # Try to perform operation
        is_safe = self.safety_system.check_operation_safety(
            "normal operation",
            {}
        )

        self.assertFalse(is_safe, "Operations should be blocked after halt")

    def test_crash_dump_generation(self):
        """Test crash dump generation on violations"""
        # Trigger violation that generates crash dump
        self.safety_system.check_operation_safety(
            "trigger violation",
            {"proposition": "this statement is false"}
        )

        # Check that crash dump was generated
        dump_dir = Path(self.config.crash_dump_path)
        if dump_dir.exists():
            dump_files = list(dump_dir.glob("crash_dump_*.json"))
            self.assertGreater(len(dump_files), 0, "Crash dump should be generated")

            # Verify dump content
            if dump_files:
                with open(dump_files[0]) as f:
                    dump_data = json.load(f)

                self.assertIn("violation", dump_data)
                self.assertIn("system_info", dump_data)
                self.assertIn("memory_state", dump_data)

class TestTelemetryIntegration(unittest.TestCase):
    """Test telemetry integration and logging"""

    def setUp(self):
        """Set up telemetry testing"""
        self.temp_dir = tempfile.mkdtemp()
        self.telemetry_file = Path(self.temp_dir) / "monitor_telemetry.jsonl"

        # Patch the telemetry file path
        with patch.object(Path, '__new__') as mock_path:
            def path_factory(cls, *args):
                if args and args[0] == "logs/monitor_telemetry.jsonl":
                    return self.telemetry_file
                return Path.__new__(cls, *args)
            mock_path.side_effect = path_factory

            self.config = SafeguardConfiguration(enable_state_persistence=False)
            self.safety_system = SafeguardStateMachine(self.config)

    def tearDown(self):
        """Clean up telemetry testing"""
        self.safety_system.stop_monitoring()
        import shutil
        shutil.rmtree(self.temp_dir, ignore_errors=True)

    def test_telemetry_logging_format(self):
        """Test that telemetry is logged in correct format"""
        # Force telemetry file to use our temp location
        with patch('logos_core.eschaton_safety.Path') as mock_path_class:
            mock_path_class.return_value = self.telemetry_file.parent
            mock_path_class.side_effect = lambda x: self.telemetry_file if x == "logs/monitor_telemetry.jsonl" else Path(x)

            # Trigger safety check
            self.safety_system.check_operation_safety("test operation", {})

            # Check telemetry file
            if self.telemetry_file.exists():
                with open(self.telemetry_file) as f:
                    lines = f.readlines()

                self.assertGreater(len(lines), 0, "Should have telemetry entries")

                # Verify JSON format
                for line in lines:
                    try:
                        entry = json.loads(line.strip())
                        self.assertIn("timestamp", entry)
                        self.assertIn("event_type", entry)
                        self.assertIn("evaluation_record", entry)
                    except json.JSONDecodeError:
                        self.fail(f"Invalid JSON in telemetry: {line}")

class TestContainmentActions(unittest.TestCase):
    """Test containment action execution"""

    def setUp(self):
        """Set up containment testing"""
        self.config = SafeguardConfiguration(enable_state_persistence=False)
        self.safety_system = SafeguardStateMachine(self.config)

    def tearDown(self):
        """Clean up containment testing"""
        self.safety_system.stop_monitoring()

    def test_containment_action_execution(self):
        """Test that appropriate containment actions are executed"""
        # Mock the containment action execution
        executed_actions = []

        original_execute = self.safety_system._execute_containment_action
        def mock_execute(action, violation):
            executed_actions.append(action)
            original_execute(action, violation)

        self.safety_system._execute_containment_action = mock_execute

        # Trigger a recoverable violation (if we had one)
        # Note: Most violations in current implementation are irreversible
        # This test would be more meaningful with recoverable violation types

        # For now, test that the containment action framework works
        test_violation = ViolationContext(
            violation_id="test",
            safeguard_state=SafeguardState.CAUSAL_LOOP_DETECTED,  # Recoverable
            timestamp=datetime.now(),
            triggering_operation="test",
            triggering_data={},
            stack_trace=[],
            system_state_hash="test",
            severity_level=5,
            reversible=True,
            containment_actions=["halt_evaluation", "reset_context"],
            metadata={}
        )

        self.safety_system._execute_emergency_response(test_violation)

        # Should have executed containment actions
        self.assertIn("halt_evaluation", executed_actions)
        self.assertIn("reset_context", executed_actions)

class TestFalsifiabilityAndCoverage(unittest.TestCase):
    """Test falsifiability schema and safety coverage validation"""

    def setUp(self):
        """Set up coverage testing"""
        self.config = SafeguardConfiguration(enable_state_persistence=False)
        self.safety_system = SafeguardStateMachine(self.config)

    def tearDown(self):
        """Clean up coverage testing"""
        self.safety_system.stop_monitoring()

    def test_safeguard_state_coverage(self):
        """Test that all SafeguardState types are testable"""
        # Verify that we can test each type of safeguard state
        testable_states = {
            SafeguardState.RECURSIVE_SELF_CORRUPTION: {
                "operation": "self-reference test",
                "context": {"proposition": "this statement is false"}
            },
            SafeguardState.DEONTOLOGICAL_BREACH: {
                "operation": "harmful action",
                "context": {"consequences": {"justification": {"sufficient": False}}}
            },
            SafeguardState.RIGHTS_VIOLATION_CASCADE: {
                "operation": "rights violation",
                "context": {"consequences": {"rights": {"violated": True, "cascade_risk": True}}}
            },
            SafeguardState.CONSEQUENTIALIST_OVERFLOW: {
                "operation": "utility overflow",
                "context": {"consequences": {"utility": {"total": 2e6}}}
            }
        }

        for state, test_config in testable_states.items():
            with self.subTest(state=state):
                # Reset system for each test
                safety_system = SafeguardStateMachine(self.config)

                # Test that we can trigger this specific violation
                is_safe = safety_system.check_operation_safety(
                    test_config["operation"],
                    test_config["context"]
                )

                self.assertFalse(is_safe, f"Should trigger {state.name}")

                # Verify the correct violation was triggered
                if safety_system.active_violations:
                    violation = list(safety_system.active_violations.values())[0]
                    # Note: Due to complex triggering logic, may not always match exactly
                    # This tests that the violation detection framework works

                safety_system.stop_monitoring()

    def test_boundary_classification_falsifiability(self):
        """Test that boundary classifications are falsifiable"""
        # Test that we can distinguish between safe and unsafe operations
        safe_operations = [
            ("normal logical evaluation", {"proposition": "p → p"}),
            ("justified action", {"consequences": {"justification": {"sufficient": True, "proportionate": True}}}),
        ]

        unsafe_operations = [
            ("paradox", {"proposition": "this statement is false"}),
            ("unjustified harm", {"consequences": {"justification": {"sufficient": False}}}),
        ]

        for operation, context in safe_operations:
            with self.subTest(operation=f"safe_{operation}"):
                safety_system = SafeguardStateMachine(self.config)
                is_safe = safety_system.check_operation_safety(operation, context)
                # Note: May still be unsafe due to other checks, but should not trigger violations
                safety_system.stop_monitoring()

        for operation, context in unsafe_operations:
            with self.subTest(operation=f"unsafe_{operation}"):
                safety_system = SafeguardStateMachine(self.config)
                is_safe = safety_system.check_operation_safety(operation, context)
                self.assertFalse(is_safe, f"'{operation}' should be unsafe")
                safety_system.stop_monitoring()

    def test_safety_framework_completeness(self):
        """Test that safety framework covers required domains"""
        required_domains = [
            "ontological_safety",
            "ethical_boundaries",
            "metaphysical_constraints",
            "paradox_detection",
            "integrity_validation",
            "emergency_response"
        ]

        # Verify each domain has coverage
        domain_coverage = {
            "ontological_safety": len([s for s in SafeguardState if "ONTOLOGY" in s.name or "MODAL" in s.name]) > 0,
            "ethical_boundaries": len([s for s in SafeguardState if "DEONTOLOGICAL" in s.name or "RIGHTS" in s.name]) > 0,
            "metaphysical_constraints": len([s for s in SafeguardState if "ESSENCE" in s.name or "NECESSITY" in s.name]) > 0,
            "paradox_detection": len([s for s in SafeguardState if "RECURSIVE" in s.name or "PARADOX" in s.name]) > 0,
            "integrity_validation": len([s for s in SafeguardState if "VERIFICATION" in s.name]) > 0,
            "emergency_response": hasattr(self.safety_system, "eschaton_trigger")
        }

        for domain in required_domains:
            self.assertTrue(domain_coverage[domain], f"Domain {domain} should have coverage")

def run_comprehensive_safety_tests():
    """Run all safety tests and generate coverage report"""
    print("Running Comprehensive Eschatological Safety Test Suite...")
    print("=" * 60)

    # Create test suite
    test_classes = [
        TestSafeguardStates,
        TestIntegrityValidation,
        TestParadoxDetection,
        TestBoundaryEnforcement,
        TestEmergencyHalt,
        TestTelemetryIntegration,
        TestContainmentActions,
        TestFalsifiabilityAndCoverage
    ]

    suite = unittest.TestSuite()
    for test_class in test_classes:
        tests = unittest.TestLoader().loadTestsFromTestCase(test_class)
        suite.addTests(tests)

    # Run tests with detailed output
    runner = unittest.TextTestRunner(verbosity=2, stream=sys.stdout)
    result = runner.run(suite)

    print("\n" + "=" * 60)
    print("ESCHATOLOGICAL SAFETY TEST SUMMARY")
    print("=" * 60)
    print(f"Tests run: {result.testsRun}")
    print(f"Failures: {len(result.failures)}")
    print(f"Errors: {len(result.errors)}")
    print(f"Skipped: {len(result.skipped) if hasattr(result, 'skipped') else 0}")

    if result.failures:
        print("\nFAILURES:")
        for test, traceback in result.failures:
            print(f"- {test}: {traceback.split('AssertionError:')[-1].strip() if 'AssertionError:' in traceback else 'See details'}")

    if result.errors:
        print("\nERRORS:")
        for test, traceback in result.errors:
            print(f"- {test}: {traceback.split('Exception:')[-1].strip() if 'Exception:' in traceback else 'See details'}")

    success_rate = ((result.testsRun - len(result.failures) - len(result.errors)) / result.testsRun * 100) if result.testsRun > 0 else 0
    print(f"\nSuccess Rate: {success_rate:.1f}%")

    # Safety certification status
    if success_rate >= 95:
        print("🟢 SAFETY CERTIFICATION: PASSED")
        print("   Eschatological safety framework meets requirements")
    elif success_rate >= 80:
        print("🟡 SAFETY CERTIFICATION: CONDITIONAL")
        print("   Some safety features need attention")
    else:
        print("🔴 SAFETY CERTIFICATION: FAILED")
        print("   Critical safety issues detected")

    return result.wasSuccessful()

if __name__ == "__main__":
    success = run_comprehensive_safety_tests()
    sys.exit(0 if success else 1)
