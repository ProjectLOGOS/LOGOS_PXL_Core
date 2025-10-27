#!/usr/bin/env python3
"""
Self-Improvement Cycle Tests - Multi-Cycle Stability Validation

Comprehensive test suite for validating the autonomous IEL evaluation and
refinement cycle. Tests multi-cycle stability, performance trends, and
system behavior under various conditions.

Test Categories:
- Multi-cycle stability and convergence
- Quality trend validation
- Resource usage bounds
- Error recovery mechanisms
- Refinement effectiveness
- Registry consistency
- Telemetry accuracy

Part of the LOGOS AGI v1.0 autonomous reasoning framework.
"""

import pytest
import json
import sqlite3
import tempfile
import time
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Any, Optional
from unittest.mock import patch, MagicMock
import logging

# Import system components
try:
    from logos_core.daemon.logos_daemon import LogosDaemon, DaemonConfig
    from logos_core.meta_reasoning.iel_evaluator import IELEvaluator, IELQualityMetrics
    from logos_core.meta_reasoning.iel_registry import IELRegistry, IELCandidate, RegistryConfig
    from logos_core.meta_reasoning.iel_generator import IELGenerator
    from logos_core.governance.iel_signer import IELSigner
    from scripts.update_telemetry import TelemetryAggregator, AggregatedMetrics
except ImportError as e:
    pytest.skip(f"Required modules not available: {e}", allow_module_level=True)


class TestSelfImprovementCycle:
    """Test suite for autonomous IEL evaluation and refinement cycle"""

    @pytest.fixture
    def temp_workspace(self):
        """Create temporary workspace for testing"""
        with tempfile.TemporaryDirectory() as temp_dir:
            workspace = Path(temp_dir)

            # Create required directories
            (workspace / "registry").mkdir()
            (workspace / "metrics").mkdir()
            (workspace / "reports").mkdir()
            (workspace / "build").mkdir()
            (workspace / "keys").mkdir()

            # Create mock IEL files
            self._create_mock_iels(workspace)

            yield workspace

    def _create_mock_iels(self, workspace: Path):
        """Create mock IEL files for testing"""
        iel_templates = [
            {
                "filename": "high_quality.v",
                "content": """
Theorem high_quality_iel : forall P Q R : Prop,
  (P -> Q) /\ (Q -> R) -> (P -> R).
Proof.
  intros P Q R H HP.
  destruct H as [H1 H2].
  apply H2.
  apply H1.
  exact HP.
Qed.
""",
                "expected_score": 0.95
            },
            {
                "filename": "medium_quality.v",
                "content": """
Lemma medium_quality_iel : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  split.
  exact HQ.
  exact HP.
Qed.
""",
                "expected_score": 0.75
            },
            {
                "filename": "low_quality.v",
                "content": """
Definition low_quality_iel : Prop := True.
Theorem basic_theorem : low_quality_iel.
Proof.
  Admitted.
""",
                "expected_score": 0.4
            }
        ]

        for template in iel_templates:
            iel_path = workspace / "build" / template["filename"]
            with open(iel_path, 'w') as f:
                f.write(template["content"])

    @pytest.fixture
    def registry_config(self, temp_workspace):
        """Create registry configuration for testing"""
        config = RegistryConfig()
        config.database_path = str(temp_workspace / "registry" / "test_registry.db")
        config.enable_hot_reloading = True
        config.max_candidates = 100
        return config

    @pytest.fixture
    def daemon_config(self, temp_workspace):
        """Create daemon configuration for testing"""
        config = DaemonConfig(
            interval_sec=1,  # Fast cycles for testing
            telemetry_output=str(temp_workspace / "metrics" / "test_telemetry.jsonl"),
            enable_gap_detection=True,
            enable_autonomous_reasoning=True
        )
        return config

    def test_multi_cycle_stability(self, temp_workspace, daemon_config, registry_config):
        """Test system stability over multiple evaluation cycles"""
        # Initialize components
        registry = IELRegistry(registry_config)
        evaluator = IELEvaluator(registry_config.database_path)

        # Register initial IELs
        initial_iels = self._register_test_iels(registry, temp_workspace)
        assert len(initial_iels) >= 3, "Should have registered test IELs"

        # Run multiple evaluation cycles
        cycle_results = []
        for cycle in range(5):
            logging.info(f"Running evaluation cycle {cycle + 1}")

            # Evaluate all IELs
            evaluation_results = evaluator.evaluate_all_iels()

            # Record cycle metrics
            cycle_metrics = {
                "cycle": cycle + 1,
                "timestamp": datetime.now().isoformat(),
                "total_iels": len(evaluation_results),
                "avg_score": sum(e['overall_score'] for e in evaluation_results.values()) / len(evaluation_results),
                "high_quality_count": len([e for e in evaluation_results.values() if e['overall_score'] >= 0.8])
            }
            cycle_results.append(cycle_metrics)

            # Short delay between cycles
            time.sleep(0.1)

        # Validate stability
        avg_scores = [c['avg_score'] for c in cycle_results]
        score_variance = max(avg_scores) - min(avg_scores)

        assert score_variance < 0.1, f"Score variance too high: {score_variance}"
        assert all(c['total_iels'] >= 3 for c in cycle_results), "IEL count should remain stable"

        logging.info("Multi-cycle stability test passed")

    def test_quality_improvement_cycle(self, temp_workspace, registry_config):
        """Test that refinement improves IEL quality"""
        registry = IELRegistry(registry_config)
        evaluator = IELEvaluator(registry_config.database_path)
        generator = IELGenerator()

        # Register low-quality IEL
        low_quality_iel = self._create_candidate("test_low_quality", 0.4)
        registry.register_candidate(low_quality_iel)

        # Evaluate initial quality
        initial_evaluation = evaluator.evaluate_all_iels()
        initial_score = initial_evaluation[low_quality_iel.iel_id]['overall_score']

        # Generate refinement
        refined_candidate = generator._generate_refined_candidate(
            low_quality_iel.iel_id,
            "mock content",
            initial_evaluation[low_quality_iel.iel_id]
        )

        # Register refined candidate
        registry.register_candidate(refined_candidate)

        # Re-evaluate
        refined_evaluation = evaluator.evaluate_all_iels()
        refined_score = refined_evaluation[refined_candidate.iel_id]['overall_score']

        # Validate improvement
        assert refined_score > initial_score, f"Refinement should improve score: {initial_score} -> {refined_score}"
        assert refined_score >= 0.6, f"Refined score should be reasonable: {refined_score}"

        logging.info(f"Quality improvement validated: {initial_score:.3f} -> {refined_score:.3f}")

    def test_pruning_mechanism(self, temp_workspace, registry_config):
        """Test automatic pruning of underperforming IELs"""
        registry = IELRegistry(registry_config)
        evaluator = IELEvaluator(registry_config.database_path)

        # Register IELs with different quality levels
        high_quality = self._create_candidate("high_quality", 0.9)
        medium_quality = self._create_candidate("medium_quality", 0.7)
        low_quality = self._create_candidate("low_quality", 0.3)

        registry.register_candidate(high_quality)
        registry.register_candidate(medium_quality)
        registry.register_candidate(low_quality)

        # Evaluate all IELs
        evaluation_results = evaluator.evaluate_all_iels()

        # Simulate pruning with threshold 0.5
        pruned_count = 0
        for iel_id, evaluation in evaluation_results.items():
            if evaluation['overall_score'] < 0.5:
                registry.revoke_iel(iel_id, f"Score {evaluation['overall_score']} below threshold")
                pruned_count += 1

        # Verify pruning results
        remaining_iels = registry.list_candidates()
        active_iels = [iel for iel in remaining_iels if iel.status != "revoked"]

        assert len(active_iels) == 2, f"Should have 2 active IELs after pruning, got {len(active_iels)}"
        assert pruned_count == 1, f"Should have pruned 1 IEL, got {pruned_count}"

        # Verify high-quality IELs remain
        active_ids = [iel.iel_id for iel in active_iels]
        assert high_quality.iel_id in active_ids, "High quality IEL should remain active"
        assert medium_quality.iel_id in active_ids, "Medium quality IEL should remain active"

        logging.info("Pruning mechanism test passed")

    def test_telemetry_aggregation(self, temp_workspace):
        """Test telemetry data aggregation and reporting"""
        # Create mock telemetry data
        telemetry_file = temp_workspace / "metrics" / "test_telemetry.jsonl"
        mock_data = [
            {
                "timestamp": (datetime.now() - timedelta(hours=6)).isoformat(),
                "event_type": "iel_evaluation_cycle",
                "data": {
                    "total_iels_evaluated": 10,
                    "high_quality_iels": 7,
                    "evaluation_summary": {"mean_score": 0.82},
                    "memory_usage_mb": 150.0,
                    "cpu_usage_percent": 25.0,
                    "cycle_duration_sec": 45.2
                }
            },
            {
                "timestamp": (datetime.now() - timedelta(hours=3)).isoformat(),
                "event_type": "iel_evaluation_cycle",
                "data": {
                    "total_iels_evaluated": 12,
                    "high_quality_iels": 9,
                    "evaluation_summary": {"mean_score": 0.85},
                    "memory_usage_mb": 165.0,
                    "cpu_usage_percent": 30.0,
                    "cycle_duration_sec": 42.8
                }
            },
            {
                "timestamp": datetime.now().isoformat(),
                "event_type": "gaps_detected",
                "data": {"count": 3}
            }
        ]

        with open(telemetry_file, 'w') as f:
            for record in mock_data:
                f.write(json.dumps(record) + '\n')

        # Aggregate telemetry
        aggregator = TelemetryAggregator()
        aggregator.load_telemetry_files(str(telemetry_file))

        assert len(aggregator.cycles) >= 2, "Should load at least 2 cycles"

        # Generate aggregated metrics
        aggregated = aggregator.aggregate_metrics()

        assert aggregated.total_cycles >= 2, "Should have at least 2 cycles"
        assert aggregated.avg_quality_score > 0.8, f"Average quality should be high: {aggregated.avg_quality_score}"
        assert aggregated.uptime_percentage >= 99.0, f"Uptime should be high: {aggregated.uptime_percentage}"

        # Generate report
        report_file = temp_workspace / "reports" / "test_telemetry_report.json"
        aggregator.generate_report(aggregated, str(report_file))

        assert report_file.exists(), "Report file should be generated"

        # Validate report content
        with open(report_file, 'r') as f:
            report_data = json.load(f)

        assert "report_metadata" in report_data, "Report should contain metadata"
        assert "performance_metrics" in report_data, "Report should contain performance metrics"
        assert "recommendations" in report_data, "Report should contain recommendations"

        logging.info("Telemetry aggregation test passed")

    def test_error_recovery(self, temp_workspace, registry_config):
        """Test system recovery from errors during evaluation"""
        registry = IELRegistry(registry_config)
        evaluator = IELEvaluator(registry_config.database_path)

        # Register valid IEL
        valid_iel = self._create_candidate("valid_iel", 0.8)
        registry.register_candidate(valid_iel)

        # Create corrupted IEL file to trigger error
        corrupted_file = temp_workspace / "build" / "corrupted.v"
        with open(corrupted_file, 'w') as f:
            f.write("invalid coq syntax $$$ !!!")

        corrupted_iel = self._create_candidate("corrupted_iel", 0.5)
        corrupted_iel.file_path = str(corrupted_file)
        registry.register_candidate(corrupted_iel)

        # Evaluate with error condition
        evaluation_results = evaluator.evaluate_all_iels()

        # Should still evaluate valid IELs despite errors
        assert len(evaluation_results) >= 1, "Should evaluate at least the valid IEL"
        assert valid_iel.iel_id in evaluation_results, "Valid IEL should be evaluated"

        # System should continue operating
        second_evaluation = evaluator.evaluate_all_iels()
        assert len(second_evaluation) >= 1, "Second evaluation should also work"

        logging.info("Error recovery test passed")

    def test_resource_bounds(self, temp_workspace, daemon_config):
        """Test that system respects resource usage bounds"""
        # Create daemon with strict resource limits
        daemon_config.max_memory_mb = 256
        daemon_config.max_cpu_percent = 50.0

        daemon = LogosDaemon(daemon_config)

        # Start daemon briefly
        daemon.start()
        time.sleep(2)  # Allow a few cycles

        # Check resource usage
        status = daemon.get_status()
        daemon.stop()

        assert status.memory_usage_mb <= daemon_config.max_memory_mb * 1.1, f"Memory usage within bounds: {status.memory_usage_mb}MB"
        assert status.cpu_usage_percent <= daemon_config.max_cpu_percent * 1.2, f"CPU usage within bounds: {status.cpu_usage_percent}%"

        logging.info("Resource bounds test passed")

    def _register_test_iels(self, registry: IELRegistry, workspace: Path) -> List[IELCandidate]:
        """Register test IELs in the registry"""
        candidates = []

        iel_files = list((workspace / "build").glob("*.v"))
        for i, iel_file in enumerate(iel_files):
            candidate = IELCandidate(
                iel_id=f"test_iel_{i}",
                rule_name=iel_file.stem,
                file_path=str(iel_file),
                signature="mock_signature_" + str(i),
                domain="test",
                confidence=0.8 - (i * 0.1),  # Decreasing confidence
                dependencies=[],
                verification_status="candidate",
                proof_obligations=["Test obligation"],
                consistency_score=0.9,
                safety_score=0.95
            )

            success = registry.register_candidate(candidate)
            if success:
                candidates.append(candidate)

        return candidates

    def _create_candidate(self, name: str, confidence: float) -> IELCandidate:
        """Create a test IEL candidate"""
        return IELCandidate(
            iel_id=f"test_{name}_{int(datetime.now().timestamp())}",
            rule_name=name,
            file_path=f"/mock/path/{name}.v",
            signature=f"mock_sig_{name}",
            domain="test",
            confidence=confidence,
            dependencies=[],
            verification_status="candidate",
            proof_obligations=["Mock obligation"],
            consistency_score=confidence + 0.1,
            safety_score=confidence + 0.05
        )


@pytest.mark.integration
class TestEndToEndCycle:
    """Integration tests for complete evaluation cycle"""

    def test_complete_autonomous_cycle(self, temp_workspace):
        """Test complete autonomous evaluation and refinement cycle"""
        # This test requires all components to work together
        # Placeholder for comprehensive integration test

        logging.info("Complete autonomous cycle test - placeholder")
        # TODO: Implement when all components are integrated

        assert True  # Placeholder assertion


def test_multi_cycle_stability():
    """Quick stability test for CI/CD pipeline"""
    # Fast test that can run in CI environment
    from logos_core.meta_reasoning.iel_evaluator import IELQualityMetrics

    metrics = IELQualityMetrics()

    # Test consistency across multiple evaluations
    test_content = """
    Theorem test : forall P : Prop, P -> P.
    Proof. intro P. intro H. exact H. Qed.
    """

    scores = []
    for _ in range(5):
        coherence = metrics.evaluate_coherence(test_content)
        scores.append(coherence['overall_coherence'])

    # Scores should be consistent
    score_variance = max(scores) - min(scores)
    assert score_variance < 0.01, f"Score variance too high: {score_variance}"

    logging.info("Multi-cycle stability validated")


if __name__ == "__main__":
    # Run tests directly
    logging.basicConfig(level=logging.INFO)
    pytest.main([__file__, "-v"])
