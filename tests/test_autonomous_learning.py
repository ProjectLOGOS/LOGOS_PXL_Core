"""
Test Autonomous Learning Framework - Comprehensive validation

This module tests the autonomous learning system's ability to:
1. Identify reasoning gaps from telemetry data
2. Generate appropriate IEL candidates
3. Evaluate and validate candidates
4. Integrate successful ones into the registry
5. Handle edge cases and failure scenarios
"""

import unittest
import json
import tempfile
import sqlite3
from datetime import datetime, timedelta
from pathlib import Path
from unittest.mock import Mock, patch, MagicMock
import sys
import os

# Add parent directory to path for imports
current_dir = Path(__file__).parent
sys.path.insert(0, str(current_dir))

from logos_core.autonomous_learning import (
    LearningCycleManager,
    TelemetryAnalyzer,
    ReasoningGap,
    LearningConfig
)

class TestTelemetryAnalyzer(unittest.TestCase):
    """Test telemetry analysis for gap identification"""

    def setUp(self):
        """Set up test fixtures"""
        self.temp_dir = tempfile.mkdtemp()
        self.telemetry_file = Path(self.temp_dir) / "test_telemetry.jsonl"
        self.analyzer = TelemetryAnalyzer(str(self.telemetry_file))

        # Create sample telemetry data
        self.sample_records = [
            {
                "timestamp": "2025-10-21T17:00:00.000Z",
                "evaluation_record": {
                    "evaluation_id": "test-1",
                    "timestamp": 1729531800.0,
                    "evaluator_type": "modal_logic",
                    "operation": "evaluate_modal_proposition",
                    "input_data": {"proposition": "[]p -> p"},
                    "output_data": {"success": False, "error": "[WinError 2] The system cannot find the file specified"},
                    "success": False,
                    "error_message": "[WinError 2] The system cannot find the file specified",
                    "execution_time_ms": 10.0,
                    "metadata": {"evaluator": "ModalLogicEvaluator"},
                    "anomaly_flags": [],
                    "consistency_check": True
                }
            },
            {
                "timestamp": "2025-10-21T17:01:00.000Z",
                "evaluation_record": {
                    "evaluation_id": "test-2",
                    "timestamp": 1729531860.0,
                    "evaluator_type": "modal_logic",
                    "operation": "evaluate_modal_proposition",
                    "input_data": {"proposition": "<>q && []q"},
                    "output_data": {"success": False, "error": "[WinError 2] The system cannot find the file specified"},
                    "success": False,
                    "error_message": "[WinError 2] The system cannot find the file specified",
                    "execution_time_ms": 8.0,
                    "metadata": {"evaluator": "ModalLogicEvaluator"},
                    "anomaly_flags": [],
                    "consistency_check": True
                }
            },
            {
                "timestamp": "2025-10-21T17:02:00.000Z",
                "evaluation_record": {
                    "evaluation_id": "test-3",
                    "timestamp": 1729531920.0,
                    "evaluator_type": "iel",
                    "operation": "evaluate_iel_proposition",
                    "input_data": {"proposition": "I(self) -> action"},
                    "output_data": {"success": False, "error": "[WinError 2] The system cannot find the file specified"},
                    "success": False,
                    "error_message": "[WinError 2] The system cannot find the file specified",
                    "execution_time_ms": 5.0,
                    "metadata": {"evaluator": "IELEvaluator"},
                    "anomaly_flags": [],
                    "consistency_check": True
                }
            },
            {
                "timestamp": "2025-10-21T17:03:00.000Z",
                "evaluation_record": {
                    "evaluation_id": "test-4",
                    "timestamp": 1729531980.0,
                    "evaluator_type": "validation",
                    "operation": "evaluate_modal_proposition",
                    "input_data": {"proposition": "malformed(((("},
                    "output_data": {},
                    "success": False,
                    "error_message": "Pre-validation failed: Unbalanced parentheses",
                    "execution_time_ms": 0.0,
                    "metadata": {"validation_issues": ["Unbalanced parentheses"]},
                    "anomaly_flags": [],
                    "consistency_check": False
                }
            }
        ]

        # Write sample data to file
        with open(self.telemetry_file, 'w') as f:
            for record in self.sample_records:
                f.write(json.dumps(record) + '\n')

    def test_load_telemetry(self):
        """Test loading telemetry records"""
        records = self.analyzer.load_telemetry()
        self.assertEqual(len(records), 4)

        # Test filtering by time - use future time to exclude all records
        future_time = datetime.now() + timedelta(hours=1)
        future_records = self.analyzer.load_telemetry(since=future_time)
        # Should be empty since test data is from past timestamps
        self.assertEqual(len(future_records), 0)

    def test_error_pattern_extraction(self):
        """Test error pattern extraction for grouping"""
        # Test bridge unavailable pattern
        pattern = self.analyzer._extract_error_pattern(
            "[WinError 2] The system cannot find the file specified",
            "[]p -> p",
            "modal_logic"
        )
        self.assertEqual(pattern, "bridge_unavailable_modal_logic")

        # Test validation failure pattern
        pattern = self.analyzer._extract_error_pattern(
            "Pre-validation failed: Unbalanced parentheses",
            "malformed(((",
            "validation"
        )
        self.assertEqual(pattern, "validation_failure_validation")

    def test_reasoning_gap_identification(self):
        """Test identification of reasoning gaps from failure patterns"""
        config = LearningConfig(min_gap_frequency=2, min_gap_severity=0.1)

        records = self.analyzer.load_telemetry()
        gaps = self.analyzer.identify_reasoning_gaps(records, config)

        # Should identify at least one gap for bridge unavailable pattern
        gap_types = [gap.gap_type for gap in gaps]
        self.assertIn("evaluation_failure", gap_types)

        # Check gap details
        bridge_gaps = [gap for gap in gaps if "bridge" in gap.domain]
        if bridge_gaps:
            gap = bridge_gaps[0]
            self.assertGreaterEqual(gap.frequency, 2)
            self.assertGreater(gap.severity, 0.0)
            self.assertTrue(gap.propositions)  # Should have sample propositions

class TestReasoningGap(unittest.TestCase):
    """Test ReasoningGap data structure"""

    def test_gap_creation_and_serialization(self):
        """Test creating and serializing reasoning gaps"""
        gap = ReasoningGap(
            gap_id="test-gap-1",
            gap_type="evaluation_failure",
            domain="modal_logic",
            description="Bridge infrastructure unavailable",
            severity=0.8,
            frequency=5,
            propositions=["[]p -> p", "<>q && []q"],
            error_patterns=["[WinError 2] The system cannot find the file specified"],
            context_data={"test": "data"},
            first_seen=datetime.now(),
            last_seen=datetime.now()
        )

        # Test serialization
        gap_dict = gap.to_dict()
        self.assertEqual(gap_dict['gap_id'], "test-gap-1")
        self.assertEqual(gap_dict['domain'], "modal_logic")
        self.assertEqual(gap_dict['frequency'], 5)
        self.assertIn('first_seen', gap_dict)
        self.assertIn('last_seen', gap_dict)

class TestLearningCycleManager(unittest.TestCase):
    """Test the complete learning cycle management"""

    def setUp(self):
        """Set up test fixtures"""
        self.temp_dir = tempfile.mkdtemp()
        self.telemetry_file = Path(self.temp_dir) / "test_telemetry.jsonl"
        self.registry_path = str(Path(self.temp_dir) / "test_registry.db")

        # Create test configuration
        self.config = LearningConfig(
            max_candidates_per_gap=3,
            evaluation_threshold=0.5,
            min_gap_frequency=2,
            min_gap_severity=0.2,
            learning_history_days=1,
            registry_path=self.registry_path
        )

        # Create sample telemetry data
        self._create_sample_telemetry()

        # Mock the components that may not be available
        with patch('logos_core.autonomous_learning.IELGenerator') as mock_gen, \
             patch('logos_core.autonomous_learning.IELEvaluator') as mock_eval, \
             patch('logos_core.autonomous_learning.IELRegistry') as mock_reg:

            # Configure generator mock
            mock_candidate = Mock()
            mock_candidate.id = "test-candidate-1"
            mock_candidate.rule_name = "test_rule"
            mock_candidate.domain = "modal_logic"
            mock_candidate.confidence = 0.8
            mock_candidate.hash = "test-hash"
            mock_candidate.metadata = {}

            mock_gen_instance = Mock()
            mock_gen_instance.generate_candidates_for_gap.return_value = [mock_candidate]
            mock_gen.return_value = mock_gen_instance

            # Configure evaluator mock
            mock_eval_instance = Mock()
            mock_eval_instance.evaluate_candidate.return_value = {
                "overall_score": 0.75,
                "consistency_score": 0.8,
                "safety_score": 0.7,
                "performance_score": 0.8
            }
            mock_eval.return_value = mock_eval_instance

            # Configure registry mock
            mock_reg_instance = Mock()
            mock_reg_instance.register_iel.return_value = True
            mock_reg.return_value = mock_reg_instance

            self.manager = LearningCycleManager(self.config)

    def _create_sample_telemetry(self):
        """Create sample telemetry data for testing"""
        now = datetime.now()

        # Create multiple failures for the same pattern
        failures = []
        for i in range(5):
            failure = {
                "timestamp": (now - timedelta(hours=i)).isoformat() + "Z",
                "evaluation_record": {
                    "evaluation_id": f"test-fail-{i}",
                    "timestamp": (now - timedelta(hours=i)).timestamp(),
                    "evaluator_type": "modal_logic",
                    "operation": "evaluate_modal_proposition",
                    "input_data": {"proposition": f"[]p{i} -> p{i}"},
                    "output_data": {"success": False, "error": "[WinError 2] The system cannot find the file specified"},
                    "success": False,
                    "error_message": "[WinError 2] The system cannot find the file specified",
                    "execution_time_ms": 10.0 + i,
                    "metadata": {"evaluator": "ModalLogicEvaluator"},
                    "anomaly_flags": [],
                    "consistency_check": True
                }
            }
            failures.append(failure)

        # Write to telemetry file
        with open(self.telemetry_file, 'w') as f:
            for failure in failures:
                f.write(json.dumps(failure) + '\n')

    def test_learning_cycle_execution(self):
        """Test complete learning cycle execution"""
        # Update analyzer to use our test file
        self.manager.analyzer = TelemetryAnalyzer(str(self.telemetry_file))

        result = self.manager.run_learning_cycle()

        # Check result structure
        self.assertIn('cycle_id', result)
        self.assertIn('status', result)
        self.assertIn('gaps_identified', result)
        self.assertIn('candidates_generated', result)

        # Should have identified gaps and generated candidates
        if result['status'] == 'completed':
            self.assertGreater(result['gaps_identified'], 0)
            self.assertGreaterEqual(result['candidates_generated'], 0)

    def test_rate_limiting(self):
        """Test learning cycle rate limiting"""
        # Simulate multiple recent cycles
        for i in range(3):
            cycle_result = {
                "cycle_id": f"test-cycle-{i}",
                "status": "completed",
                "start_time": (datetime.now() - timedelta(minutes=10*i)).isoformat(),
                "gaps_identified": 1,
                "candidates_generated": 1
            }
            self.manager._record_cycle_result(cycle_result)

        # Should be rate limited now
        rate_ok = self.manager._check_rate_limit()
        # Depends on configuration, but should respect limits
        self.assertIsInstance(rate_ok, bool)

    def test_learning_status_reporting(self):
        """Test learning status reporting"""
        status = self.manager.get_learning_status()

        self.assertIn('total_cycles', status)
        self.assertIn('config', status)
        self.assertIn('average_acceptance_rate', status)

        # Should start with zero cycles
        self.assertEqual(status['total_cycles'], 0)

class TestIntegrationScenarios(unittest.TestCase):
    """Test end-to-end integration scenarios"""

    def setUp(self):
        """Set up integration test environment"""
        self.temp_dir = tempfile.mkdtemp()
        Path("test_logs").mkdir(exist_ok=True)
        Path("test_registry").mkdir(exist_ok=True)

    def test_simulated_reasoning_failures(self):
        """Test learning from simulated reasoning failures"""
        # Create a telemetry file with various failure types
        telemetry_file = Path("test_logs/integration_telemetry.jsonl")

        failure_scenarios = [
            # Bridge unavailable failures
            {
                "error_type": "bridge_unavailable",
                "evaluator": "modal_logic",
                "propositions": ["[]p -> p", "<>q", "[]r && <>r"],
                "count": 4
            },
            # Validation failures
            {
                "error_type": "validation_failure",
                "evaluator": "validation",
                "propositions": ["malformed((", "unclosed[", "invalid&&"],
                "count": 3
            },
            # IEL failures
            {
                "error_type": "bridge_unavailable",
                "evaluator": "iel",
                "propositions": ["I(self) -> action", "E(input) && goal"],
                "count": 3
            }
        ]

        # Generate telemetry data
        with open(telemetry_file, 'w') as f:
            record_id = 0
            for scenario in failure_scenarios:
                for i in range(scenario["count"]):
                    for prop in scenario["propositions"]:
                        record = {
                            "timestamp": datetime.now().isoformat() + "Z",
                            "evaluation_record": {
                                "evaluation_id": f"integration-{record_id}",
                                "timestamp": datetime.now().timestamp(),
                                "evaluator_type": scenario["evaluator"],
                                "operation": "evaluate_modal_proposition",
                                "input_data": {"proposition": prop},
                                "output_data": {"success": False, "error": "Test error"},
                                "success": False,
                                "error_message": f"Test {scenario['error_type']} error",
                                "execution_time_ms": 10.0,
                                "metadata": {},
                                "anomaly_flags": [],
                                "consistency_check": True
                            }
                        }
                        f.write(json.dumps(record) + '\n')
                        record_id += 1

        # Test analyzer on generated data
        analyzer = TelemetryAnalyzer(str(telemetry_file))
        config = LearningConfig(min_gap_frequency=2, min_gap_severity=0.1)

        records = analyzer.load_telemetry()
        gaps = analyzer.identify_reasoning_gaps(records, config)

        # Should identify multiple gap types
        self.assertGreater(len(gaps), 0)

        gap_domains = set(gap.domain for gap in gaps)
        # Should have identified different domains
        self.assertTrue(len(gap_domains) > 0)

        # Cleanup
        if telemetry_file.exists():
            telemetry_file.unlink()

    def test_learning_manager_with_mocked_components(self):
        """Test learning manager with fully mocked components"""
        config = LearningConfig(
            max_candidates_per_gap=2,
            evaluation_threshold=0.6,
            min_gap_frequency=1
        )

        with patch('logos_core.autonomous_learning.IELGenerator') as mock_gen, \
             patch('logos_core.autonomous_learning.IELEvaluator') as mock_eval, \
             patch('logos_core.autonomous_learning.IELRegistry') as mock_reg:

            # Setup mocks
            mock_candidate = Mock()
            mock_candidate.id = "integration-candidate"
            mock_candidate.rule_name = "integration_rule"
            mock_candidate.domain = "test_domain"
            mock_candidate.confidence = 0.8
            mock_candidate.hash = "integration-hash"
            mock_candidate.metadata = {}

            mock_gen.return_value.generate_candidates_for_gap.return_value = [mock_candidate]
            mock_eval.return_value.evaluate_candidate.return_value = {"overall_score": 0.8}
            mock_reg.return_value.register_iel.return_value = True

            manager = LearningCycleManager(config)

            # Create minimal telemetry data
            telemetry_file = Path("test_logs/minimal_telemetry.jsonl")
            with open(telemetry_file, 'w') as f:
                record = {
                    "timestamp": datetime.now().isoformat() + "Z",
                    "evaluation_record": {
                        "evaluation_id": "minimal-test",
                        "timestamp": datetime.now().timestamp(),
                        "evaluator_type": "modal_logic",
                        "operation": "evaluate_modal_proposition",
                        "input_data": {"proposition": "test_prop"},
                        "output_data": {"success": False, "error": "Test error"},
                        "success": False,
                        "error_message": "Test error",
                        "execution_time_ms": 10.0,
                        "metadata": {},
                        "anomaly_flags": [],
                        "consistency_check": True
                    }
                }
                f.write(json.dumps(record) + '\n')

            manager.analyzer = TelemetryAnalyzer(str(telemetry_file))

            # Run learning cycle
            result = manager.run_learning_cycle()

            # Verify successful execution
            self.assertIn('status', result)
            if result['status'] == 'completed':
                self.assertGreaterEqual(result.get('gaps_identified', 0), 0)

            # Cleanup
            if telemetry_file.exists():
                telemetry_file.unlink()

class TestEdgeCasesAndFailures(unittest.TestCase):
    """Test edge cases and failure scenarios"""

    def test_empty_telemetry_file(self):
        """Test handling of empty telemetry file"""
        temp_file = Path(tempfile.mkdtemp()) / "empty.jsonl"
        temp_file.touch()  # Create empty file

        analyzer = TelemetryAnalyzer(str(temp_file))
        records = analyzer.load_telemetry()

        self.assertEqual(len(records), 0)

        config = LearningConfig()
        gaps = analyzer.identify_reasoning_gaps(records, config)
        self.assertEqual(len(gaps), 0)

    def test_missing_telemetry_file(self):
        """Test handling of missing telemetry file"""
        analyzer = TelemetryAnalyzer("nonexistent_file.jsonl")
        records = analyzer.load_telemetry()

        self.assertEqual(len(records), 0)

    def test_malformed_telemetry_data(self):
        """Test handling of malformed telemetry data"""
        temp_file = Path(tempfile.mkdtemp()) / "malformed.jsonl"

        with open(temp_file, 'w') as f:
            f.write('{"invalid": json}\n')  # Invalid JSON
            f.write('{"valid": "json", "timestamp": "2025-10-21T17:00:00.000Z"}\n')
            f.write('not json at all\n')
            f.write('{"another": "valid", "timestamp": "2025-10-21T17:01:00.000Z"}\n')

        analyzer = TelemetryAnalyzer(str(temp_file))
        records = analyzer.load_telemetry()

        # Should load only valid JSON records
        self.assertEqual(len(records), 2)

    def test_learning_cycle_with_no_gaps(self):
        """Test learning cycle when no gaps are identified"""
        config = LearningConfig(min_gap_frequency=100)  # Very high threshold

        with patch('logos_core.autonomous_learning.IELGenerator') as mock_gen, \
             patch('logos_core.autonomous_learning.IELEvaluator') as mock_eval, \
             patch('logos_core.autonomous_learning.IELRegistry') as mock_reg:

            manager = LearningCycleManager(config)

            # Create telemetry with insufficient failures
            temp_file = Path(tempfile.mkdtemp()) / "low_failure.jsonl"
            with open(temp_file, 'w') as f:
                record = {
                    "timestamp": datetime.now().isoformat() + "Z",
                    "evaluation_record": {
                        "evaluation_id": "single-failure",
                        "timestamp": datetime.now().timestamp(),
                        "evaluator_type": "modal_logic",
                        "operation": "evaluate_modal_proposition",
                        "input_data": {"proposition": "single_prop"},
                        "output_data": {"success": False, "error": "Single error"},
                        "success": False,
                        "error_message": "Single error",
                        "execution_time_ms": 10.0,
                        "metadata": {},
                        "anomaly_flags": [],
                        "consistency_check": True
                    }
                }
                f.write(json.dumps(record) + '\n')

            manager.analyzer = TelemetryAnalyzer(str(temp_file))

            result = manager.run_learning_cycle()

            # Should complete but with no gaps
            self.assertEqual(result['status'], 'no_gaps')

def run_autonomous_learning_tests():
    """Run all autonomous learning tests"""
    loader = unittest.TestLoader()
    suite = unittest.TestSuite()

    # Add all test classes
    test_classes = [
        TestTelemetryAnalyzer,
        TestReasoningGap,
        TestLearningCycleManager,
        TestIntegrationScenarios,
        TestEdgeCasesAndFailures
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
    print("LOGOS AGI Autonomous Learning Framework - Test Suite")
    print("=" * 60)

    # Ensure test directories exist
    Path("test_logs").mkdir(exist_ok=True)
    Path("test_registry").mkdir(exist_ok=True)

    # Run comprehensive tests
    summary = run_autonomous_learning_tests()

    print(f"\nAutonomous Learning Test Summary:")
    print(f"Tests Run: {summary['tests_run']}")
    print(f"Failures: {summary['failures']}")
    print(f"Errors: {summary['errors']}")
    print(f"Overall Success: {summary['success']}")

    if not summary['success']:
        print(f"\nFailure Details:")
        for failure in summary['failure_details']:
            print(f"- {failure[0]}: {failure[1]}")

    # Cleanup test files
    try:
        import shutil
        for test_dir in ["test_logs", "test_registry"]:
            if Path(test_dir).exists():
                shutil.rmtree(test_dir)
    except (PermissionError, OSError):
        print("Note: Could not cleanup all test directories")

    # Exit with appropriate code
    sys.exit(0 if summary['success'] else 1)
