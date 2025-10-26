"""
Quick demo of Extensions Loader - validates initialization and status
"""

import sys
import os
sys.path.insert(0, os.path.abspath('.'))

from boot.extensions_loader import extensions_manager

def main():
    print("=" * 70)
    print("LOGOS Extensions Loader - Initialization Demo")
    print("=" * 70)
    print()

    # Initialize without PXL client (bypass mode for demo)
    print("Initializing extensions manager (bypass mode)...")
    print()

    success = extensions_manager.initialize(pxl_client=None)

    print()
    print("=" * 70)
    print("Initialization Complete!")
    print("=" * 70)
    print()

    # Get status
    status = extensions_manager.get_status()
    print("📊 Extensions Status:")
    print(f"  Initialized: {status['initialized']}")
    print(f"  Audit Entries: {status['audit_entries']}")
    print()

    print("📚 Library Availability:")
    for lib_name, lib_info in status['libraries'].items():
        status_icon = "✅" if lib_info['loaded'] else "❌"
        print(f"  {status_icon} {lib_name:25s} - {'Available' if lib_info['loaded'] else 'Not installed'}")
    print()

    # Test some orchestration methods
    print("=" * 70)
    print("Testing Orchestration Methods")
    print("=" * 70)
    print()

    # Test 1: NetworkX Graph
    if extensions_manager.is_available('networkx'):
        print("🔷 Testing NetworkX graph operations...")
        nodes = ['Logic', 'Proof', 'Inference', 'Validation']
        edges = [('Logic', 'Proof'), ('Proof', 'Inference'), ('Inference', 'Validation')]
        graph = extensions_manager.build_graph(nodes, edges)
        if graph:
            analysis = extensions_manager.analyze_graph(graph)
            print(f"  Graph created: {analysis['num_nodes']} nodes, {analysis['num_edges']} edges")
            print(f"  Density: {analysis['density']:.3f}")
            print("  ✅ NetworkX operational")
        print()

    # Test 2: PyTorch
    if extensions_manager.is_available('pytorch'):
        print("🔷 Testing PyTorch tensor operations...")
        tensor = extensions_manager.create_tensor([[1.0, 2.0], [3.0, 4.0]])
        if tensor is not None:
            print(f"  Tensor created: shape {tensor.shape}")
            print("  ✅ PyTorch operational")
        print()

    # Test 3: Sentence Embeddings
    if extensions_manager.is_available('sentence_transformers'):
        print("🔷 Testing Sentence Transformers...")
        text = "LOGOS validates formal proofs with provable correctness"
        embedding = extensions_manager.embed_sentence(text)
        if embedding:
            print(f"  Embedded sentence: {len(embedding)} dimensions")
            print(f"  Sample values: {embedding[:5]}")
            print("  ✅ Sentence Transformers operational")
        print()

    # Test 4: Kalman Filter
    if extensions_manager.is_available('filterpy') or extensions_manager.is_available('pykalman'):
        print("🔷 Testing Kalman filter...")
        measurements = [1.0, 1.2, 0.9, 1.1, 1.3, 0.8, 1.0, 1.1]
        filtered = extensions_manager.kalman_filter(measurements)
        if filtered:
            print(f"  Input measurements: {measurements}")
            print(f"  Filtered output: {[f'{x:.3f}' for x in filtered]}")
            print("  ✅ Kalman filtering operational")
        print()

    # Test 5: Scikit-learn
    if extensions_manager.is_available('scikit_learn'):
        print("🔷 Testing scikit-learn classification...")
        X_train = [[0, 0], [1, 1], [2, 2], [3, 3]]
        y_train = [0, 0, 1, 1]
        X_test = [[0.5, 0.5], [2.5, 2.5]]
        predictions = extensions_manager.sklearn_classify(X_train, y_train, X_test)
        if predictions is not None:
            print(f"  Test predictions: {predictions}")
            print("  ✅ Scikit-learn operational")
        print()

    # Show audit log summary
    print("=" * 70)
    print("📋 Audit Log Summary")
    print("=" * 70)
    audit_log = extensions_manager.get_audit_log()

    allowed = sum(1 for entry in audit_log if entry['decision'] == 'allow')
    denied = sum(1 for entry in audit_log if entry['decision'] == 'deny')

    print(f"  Total audit entries: {len(audit_log)}")
    print(f"  Libraries loaded: {allowed}")
    print(f"  Libraries failed: {denied}")
    print()

    # Show recent audit entries
    print("Recent audit entries:")
    for entry in audit_log[-5:]:
        status_icon = "✅" if entry['decision'] == 'allow' else "❌"
        lib_name = entry['library']
        status = entry['status']
        print(f"  {status_icon} {lib_name:20s} - {status}")

    print()
    print("=" * 70)
    print("Demo Complete!")
    print("=" * 70)

if __name__ == '__main__':
    main()
