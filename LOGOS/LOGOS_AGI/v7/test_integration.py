"""
LOGOS AGI v7 - Integration Test
==============================

Basic integration test verifying all v7 components work together
with proof-gated validation and trinity vector coherence.
"""

import asyncio
import logging
import sys
import os
from typing import Dict, Any

# Add LOGOS v7 to path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))


def test_imports():
    """Test that all v7 components can be imported"""
    print("Testing component imports...")

    try:
        from LOGOS_AGI.v7.adaptive_reasoning.bayesian_inference import (
            UnifiedBayesianInferencer,
            TrinityVector,
        )

        print("  ✓ Bayesian inference components")

        from LOGOS_AGI.v7.adaptive_reasoning.semantic_transformers import UnifiedSemanticTransformer

        print("  ✓ Semantic transformer components")

        from LOGOS_AGI.v7.adaptive_reasoning.torch_adapters import UnifiedTorchAdapter

        print("  ✓ Torch adapter components")

        from LOGOS_AGI.v7.runtime_services.core_service import UnifiedRuntimeService, RequestType

        print("  ✓ Runtime service components")

        from LOGOS_AGI.v7.integration.adaptive_interface import (
            LOGOSv7UnifiedInterface,
            create_logos_v7_interface,
            UnifiedRequest,
            OperationMode,
        )

        print("  ✓ Unified interface components")

        return True

    except ImportError as e:
        print(f"  ✗ Import failed: {e}")
        return False


def test_component_initialization():
    """Test component initialization"""
    print("\nTesting component initialization...")

    try:
        # Import with fallback handling
        from LOGOS_AGI.v7.adaptive_reasoning.bayesian_inference import UnifiedBayesianInferencer
        from LOGOS_AGI.v7.adaptive_reasoning.semantic_transformers import UnifiedSemanticTransformer
        from LOGOS_AGI.v7.adaptive_reasoning.torch_adapters import UnifiedTorchAdapter
        from LOGOS_AGI.v7.runtime_services.core_service import UnifiedRuntimeService

        # Initialize components
        bayesian = UnifiedBayesianInferencer()
        print("  ✓ Bayesian inferencer initialized")

        semantic = UnifiedSemanticTransformer()
        print("  ✓ Semantic transformer initialized")

        torch_adapter = UnifiedTorchAdapter()
        print("  ✓ Torch adapter initialized")

        runtime = UnifiedRuntimeService(enable_messaging=False)
        print("  ✓ Runtime service initialized")

        return True

    except Exception as e:
        print(f"  ✗ Initialization failed: {e}")
        return False


def test_trinity_vector_creation():
    """Test trinity vector creation and validation"""
    print("\nTesting trinity vector operations...")

    try:
        from LOGOS_AGI.v7.adaptive_reasoning.bayesian_inference import TrinityVector

        # Create trinity vector
        trinity = TrinityVector(e_identity=0.4, g_experience=0.3, t_logos=0.3, confidence=0.8)

        print(
            f"  ✓ Trinity vector created: E={trinity.e_identity}, G={trinity.g_experience}, T={trinity.t_logos}"
        )
        print(f"  ✓ Confidence: {trinity.confidence}")

        return True

    except Exception as e:
        print(f"  ✗ Trinity vector test failed: {e}")
        return False


async def test_unified_interface():
    """Test unified interface with basic operations"""
    print("\nTesting unified interface...")

    try:
        from LOGOS_AGI.v7.integration.adaptive_interface import (
            create_logos_v7_interface,
            UnifiedRequest,
            OperationMode,
        )

        # Create interface
        interface = create_logos_v7_interface(
            verification_threshold=0.6,  # Lower threshold for testing
            enable_neural_processing=False,  # Disable to avoid GPU requirements
            enable_distributed_runtime=False,
        )
        print("  ✓ Unified interface created")

        # Test query operation
        query_request = UnifiedRequest(
            operation="query",
            input_data={"text": "What is intelligence?"},
            mode=OperationMode.BALANCED,
        )

        query_response = await interface.process_unified_request(query_request)
        print(f"  ✓ Query processed: {query_response.result.value}")
        print(f"  ✓ Confidence: {query_response.confidence_score:.3f}")

        # Test inference operation
        inference_request = UnifiedRequest(
            operation="inference",
            input_data={
                "data": {"keywords": ["reasoning", "logic", "intelligence"]},
                "inference_type": "basic",
            },
            mode=OperationMode.CONSERVATIVE,
        )

        inference_response = await interface.process_unified_request(inference_request)
        print(f"  ✓ Inference processed: {inference_response.result.value}")
        print(
            f"  ✓ Trinity vector: E={inference_response.trinity_vector.e_identity:.2f}, "
            f"G={inference_response.trinity_vector.g_experience:.2f}, "
            f"T={inference_response.trinity_vector.t_logos:.2f}"
        )

        # Test transformation operation
        transformation_request = UnifiedRequest(
            operation="transformation",
            input_data={
                "source": "The system demonstrates intelligent behavior",
                "target": {"type": "semantic_shift", "tone": "formal"},
            },
            mode=OperationMode.BALANCED,
        )

        transformation_response = await interface.process_unified_request(transformation_request)
        print(f"  ✓ Transformation processed: {transformation_response.result.value}")

        # Check system status
        status = interface.get_system_status()
        print(
            f"  ✓ System status: {status['processing_statistics']['success_rate_percent']:.1f}% success rate"
        )

        return True

    except Exception as e:
        print(f"  ✗ Unified interface test failed: {e}")
        import traceback

        traceback.print_exc()
        return False


def test_proof_gate_validation():
    """Test proof gate validation"""
    print("\nTesting proof gate validation...")

    try:
        from LOGOS_AGI.v7.integration.adaptive_interface import (
            ProofGateInterface,
            UnifiedRequest,
            OperationMode,
        )
        from LOGOS_AGI.v7.adaptive_reasoning.bayesian_inference import TrinityVector

        # Create proof gate
        proof_gate = ProofGateInterface(verification_threshold=0.7)

        # Test valid request
        valid_request = UnifiedRequest(
            operation="query",
            input_data={"text": "Test query"},
            mode=OperationMode.BALANCED,
            trinity_context=TrinityVector(
                e_identity=0.3, g_experience=0.4, t_logos=0.3, confidence=0.8
            ),
        )

        is_valid, metadata = proof_gate.validate_unified_operation(valid_request)
        print(
            f"  ✓ Valid request validation: {is_valid} (score: {metadata['validation_score']:.3f})"
        )

        # Test invalid request
        invalid_request = UnifiedRequest(
            operation="invalid_operation", input_data={}, mode=OperationMode.BALANCED
        )

        is_valid, metadata = proof_gate.validate_unified_operation(invalid_request)
        print(
            f"  ✓ Invalid request validation: {is_valid} (score: {metadata['validation_score']:.3f})"
        )

        return True

    except Exception as e:
        print(f"  ✗ Proof gate test failed: {e}")
        return False


async def run_integration_tests():
    """Run all integration tests"""
    print("LOGOS AGI v7 - Integration Test Suite")
    print("=" * 40)

    # Configure minimal logging
    logging.basicConfig(level=logging.WARNING)

    tests = [
        ("Import Test", test_imports),
        ("Component Initialization", test_component_initialization),
        ("Trinity Vector Operations", test_trinity_vector_creation),
        ("Proof Gate Validation", test_proof_gate_validation),
        ("Unified Interface", test_unified_interface),
    ]

    passed = 0
    total = len(tests)

    for test_name, test_func in tests:
        print(f"\n{test_name}:")
        print("-" * (len(test_name) + 1))

        try:
            if asyncio.iscoroutinefunction(test_func):
                result = await test_func()
            else:
                result = test_func()

            if result:
                passed += 1
                print(f"  ✓ {test_name} PASSED")
            else:
                print(f"  ✗ {test_name} FAILED")

        except Exception as e:
            print(f"  ✗ {test_name} ERROR: {e}")

    print(f"\n{'='*40}")
    print(f"Integration Test Results: {passed}/{total} tests passed")
    print(f"Success rate: {(passed/total)*100:.1f}%")

    if passed == total:
        print("🎉 All integration tests passed!")
        return True
    else:
        print("⚠️  Some integration tests failed")
        return False


if __name__ == "__main__":
    # Run integration tests
    success = asyncio.run(run_integration_tests())

    # Exit with appropriate code
    sys.exit(0 if success else 1)
