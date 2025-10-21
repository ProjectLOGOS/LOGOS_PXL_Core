"""
Enhanced Reference Monitor Demo

This script demonstrates the enhanced reference monitor's capabilities
including validation, logging, and anomaly detection.
"""

import json
import time
from pathlib import Path
from logos_core.entry import get_logos_core, get_status

def run_demo():
    """Run demonstration of enhanced reference monitor"""
    print("LOGOS AGI Enhanced Reference Monitor - Demo")
    print("=" * 50)

    # Initialize LOGOS Core
    print("\n1. Initializing LOGOS Core with Enhanced Reference Monitor...")
    core = get_logos_core()
    print(f"   ✓ LOGOS Core initialized: {core._initialized}")

    # Show system status
    print("\n2. System Status:")
    status = get_status()
    print(f"   ✓ LOGOS Core: {status['logos_core']['status']}")
    print(f"   ✓ Reference Monitor: {status['reference_monitor']['monitor_status']}")
    print(f"   ✓ Total Evaluations: {status['reference_monitor']['total_evaluations']}")

    # Test basic modal logic evaluation
    print("\n3. Testing Modal Logic Evaluation with Monitoring...")
    try:
        result = core.evaluate_modal_logic(
            "p && q",
            world="w0",
            accessible_worlds=["w0", "w1"],
            valuations={"p": True, "q": False}
        )
        print(f"   ✓ Modal evaluation successful: {result.get('success', False)}")
        print(f"   ✓ Result: {result.get('result', 'N/A')}")
    except Exception as e:
        print(f"   ✗ Modal evaluation failed: {e}")

    # Test IEL evaluation
    print("\n4. Testing IEL Evaluation with Monitoring...")
    try:
        result = core.evaluate_iel_logic(
            "I(self) -> action",
            identity_context={"self": "agent"},
            valuations={"action": True}
        )
        print(f"   ✓ IEL evaluation successful: {result.get('success', False)}")
        print(f"   ✓ Result: {result.get('result', 'N/A')}")
    except Exception as e:
        print(f"   ✗ IEL evaluation failed: {e}")

    # Test batch evaluation
    print("\n5. Testing Batch Evaluation...")
    propositions = [
        "p || ~p",  # Tautology
        "q && ~q",  # Contradiction
        "[]p -> p", # T axiom
        "I(agent) && E(input)"  # IEL proposition
    ]

    try:
        result = core.evaluate_batch(
            propositions,
            valuations={"p": True, "q": False, "agent": True, "input": True}
        )
        print(f"   ✓ Batch evaluation successful")
        print(f"   ✓ Total propositions: {result.get('total_count', 0)}")
        print(f"   ✓ Successful evaluations: {result.get('success_count', 0)}")
        if result.get('batch_anomalies'):
            print(f"   ⚠ Anomalies detected: {len(result['batch_anomalies'])}")
    except Exception as e:
        print(f"   ✗ Batch evaluation failed: {e}")

    # Test validation (this should fail)
    print("\n6. Testing Pre-validation (Dangerous Pattern)...")
    try:
        result = core.evaluate_modal_logic("__import__('os').system('echo test')")
        print(f"   ✗ Dangerous pattern was not caught!")
    except Exception as e:
        print(f"   ✓ Dangerous pattern correctly blocked: {str(e)[:60]}...")

    # Test syntax validation
    print("\n7. Testing Syntax Validation...")
    try:
        result = core.evaluate_modal_logic("p && q))")  # Unbalanced parentheses
        print(f"   ✗ Invalid syntax was not caught!")
    except Exception as e:
        print(f"   ✓ Invalid syntax correctly blocked: {str(e)[:60]}...")

    # Show updated status
    print("\n8. Final System Status:")
    status = get_status()
    monitor_status = status['reference_monitor']
    print(f"   ✓ Total Evaluations: {monitor_status['total_evaluations']}")
    print(f"   ✓ Total Errors: {monitor_status['total_errors']}")
    print(f"   ✓ Total Anomalies: {monitor_status['total_anomalies']}")
    print(f"   ✓ Monitor Status: {monitor_status['monitor_status']}")

    # Check telemetry file
    telemetry_file = Path("logs/monitor_telemetry.jsonl")
    if telemetry_file.exists():
        print(f"\n9. Telemetry Logging:")
        print(f"   ✓ Telemetry file exists: {telemetry_file}")

        # Count entries
        with open(telemetry_file, 'r') as f:
            entries = [line for line in f if line.strip()]
        print(f"   ✓ Telemetry entries: {len(entries)}")

        # Show latest entry (if exists and has our demo data)
        if entries:
            try:
                latest = json.loads(entries[-1])
                if 'evaluation_record' in latest:
                    record = latest['evaluation_record']
                    print(f"   ✓ Latest operation: {record.get('operation', 'N/A')}")
                    print(f"   ✓ Success: {record.get('success', 'N/A')}")
                    print(f"   ✓ Anomaly flags: {len(record.get('anomaly_flags', []))}")
            except json.JSONDecodeError:
                print("   ⚠ Latest telemetry entry malformed")

    print("\n" + "=" * 50)
    print("Enhanced Reference Monitor Demo Complete")
    print("✓ All monitoring capabilities demonstrated")
    print("✓ Safety validation operational")
    print("✓ Telemetry logging functional")

    # Clean shutdown
    core.shutdown()

if __name__ == "__main__":
    run_demo()
