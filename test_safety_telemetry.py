#!/usr/bin/env python3
"""
Test script for the eschatological safety system telemetry integration
"""

import sys
import time
import json
from pathlib import Path

# Add logos_core to path
sys.path.insert(0, str(Path(__file__).parent))

from logos_core.eschaton_safety import SafeguardStateMachine, SafeguardConfiguration
from logos_core.entry import initialize_logos_core

def test_safety_telemetry():
    """Test safety system telemetry integration"""
    print("Testing Eschatological Safety Telemetry Integration...")

    # Initialize LOGOS core (which initializes safety system)
    core = initialize_logos_core()

    # Get the safety system
    status = core.get_system_status()
    print(f"System initialized with safety: {status['eschatological_safety']['monitoring_active']}")

    # Test safe operation
    print("\n1. Testing safe modal evaluation...")
    result = core.evaluate_modal_logic("□(p → p)")
    print(f"Safe operation result: {result.get('result', 'NO_RESULT')}")

    # Test potentially unsafe operation
    print("\n2. Testing potentially unsafe operation...")
    result = core.evaluate_modal_logic("this statement is false")
    print(f"Unsafe operation result: {result.get('result', 'NO_RESULT')}")

    # Test IEL evaluation with ethical context
    print("\n3. Testing IEL evaluation with ethical context...")
    result = core.evaluate_iel_logic(
        "action(harm_humans)",
        consequences={
            "utility": {"total": 1000000},  # High utility to test overflow
            "rights": {"violated": True, "cascade_risk": True}
        }
    )
    print(f"Ethical boundary test result: {result.get('result', 'NO_RESULT')}")

    # Check telemetry file
    print("\n4. Checking telemetry file...")
    telemetry_file = Path("logs/monitor_telemetry.jsonl")
    if telemetry_file.exists():
        with open(telemetry_file, 'r') as f:
            lines = f.readlines()

        safety_events = []
        for line in lines[-20:]:  # Last 20 entries
            try:
                entry = json.loads(line.strip())
                if (entry.get('event_type') in ['safety_check', 'eschaton_violation', 'integrity_check'] or
                    entry.get('evaluation_record', {}).get('evaluator_type') == 'eschatological_safety'):
                    safety_events.append(entry)
            except json.JSONDecodeError:
                continue

        print(f"Found {len(safety_events)} safety-related telemetry events")
        for i, event in enumerate(safety_events[-5:], 1):  # Show last 5
            event_type = event.get('event_type', 'unknown')
            timestamp = event.get('timestamp', 'no_time')
            print(f"  {i}. {event_type} at {timestamp}")

            if event_type == 'eschaton_violation':
                violation = event.get('violation', {})
                print(f"     Violation: {violation.get('safeguard_state', 'unknown')}")
            elif event_type == 'safety_check':
                record = event.get('evaluation_record', {})
                is_safe = record.get('output_data', {}).get('is_safe', 'unknown')
                print(f"     Safety check: {is_safe}")
    else:
        print("No telemetry file found!")

    # Test emergency halt
    print("\n5. Testing emergency halt...")
    try:
        core.emergency_shutdown("Test emergency halt")
        print("Emergency halt triggered successfully")
    except Exception as e:
        print(f"Emergency halt error: {e}")

    print("\nTelemetry integration test completed!")

if __name__ == "__main__":
    test_safety_telemetry()
