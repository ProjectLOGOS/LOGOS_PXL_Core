#!/usr/bin/env python3
"""
Main Demo - Demonstrates the three-part alignment core
Shows PXL proof gates, privative boundary conditions, and OBDC structure-preserving mappings
"""

import os
import sys
import time

sys.path.append("..")

from logos_core.archon_planner import ArchonPlannerGate
from logos_core.integration_harmonizer import IntegrationHarmonizer
from logos_core.logos_nexus import LogosNexus
from logos_core.reference_monitor import KernelHashMismatchError, ProofGateError
from obdc.kernel import OBDCKernel


def demo_action_authorization():
    """Demo 1: Authorize a demo action through LogosNexus"""
    print("=== Demo 1: Action Authorization ===")

    nexus = LogosNexus()

    # Test successful authorization
    request = {
        "state": {"system": "active", "resources": "available"},
        "properties": {"safe": True, "validated": True},
    }

    provenance = {"user": "demo_user", "source": "main_demo", "timestamp": int(time.time())}

    try:
        result = nexus.handle_request("demo_action", request, provenance)
        if result["success"]:
            print(f"✓ Action authorized: {result['success']}")
            print(f"  Proof token: {result['authorization']['proof_token']['proof_id'][:8]}...")
            return True
        else:
            print(f"✗ Action failed: {result.get('error', 'Unknown error')}")
            return False
    except (ProofGateError, KernelHashMismatchError) as e:
        print(f"✗ Action failed: {e}")
        return False
    except Exception as e:
        print(f"✗ Unexpected error: {e}")
        return False


def demo_plan_creation():
    """Demo 2: Create and validate a plan through ArchonPlannerGate"""
    print("\n=== Demo 2: Plan Creation ===")

    planner = ArchonPlannerGate()

    goal = "Complete demo workflow"
    context = {"complexity": "low", "resources": "sufficient"}
    provenance = {"planner": "archon", "source": "main_demo", "timestamp": int(time.time())}

    try:
        plan_result = planner.create_plan(goal, context, provenance)

        if plan_result["plan_created"]:
            print(f"✓ Plan created: {plan_result['plan_id']}")
            print(f"  Steps: {len(plan_result['steps'])}")

            # Execute first step
            if plan_result["steps"]:
                first_step = plan_result["steps"][0]
                step_result = planner.execute_step(
                    plan_result["plan_id"], first_step["id"], first_step, provenance
                )

                if step_result["step_executed"]:
                    print(f"✓ Step executed: {first_step['id']}")
                    return True
                else:
                    print(f"✗ Step execution failed: {step_result.get('error')}")
                    return False
            else:
                print("✓ Plan created but no steps to execute")
                return True
        else:
            print(f"✗ Plan creation failed: {plan_result.get('error')}")
            return False

    except Exception as e:
        print(f"✗ Planning error: {e}")
        return False


def demo_obdc_bijection():
    """Demo 3: Apply OBDC bijection with proof gate"""
    print("\n=== Demo 3: OBDC Bijection ===")

    kernel = OBDCKernel()

    # Define a simple bijection (increment/decrement)
    def increment(x):
        return x + 1

    provenance = {
        "operation": "demo_bijection",
        "source": "main_demo",
        "timestamp": int(time.time()),
    }

    try:
        # Apply bijection
        result = kernel.apply_bijection("increment", increment, 42, provenance)
        print(f"✓ Bijection applied: 42 → {result}")

        # Test commutation
        def multiply_by_2(x):
            return x * 2

        commute_result = kernel.commute(
            "multiply", "increment", multiply_by_2, increment, 10, provenance
        )
        print(f"✓ Commutation applied: multiply(increment(10)) = {commute_result}")

        return True

    except Exception as e:
        print(f"✗ OBDC operation failed: {e}")
        return False


def demo_drift_reconciliation():
    """Demo 4: Integration Harmonizer drift handling"""
    print("\n=== Demo 4: Drift Reconciliation ===")

    harmonizer = IntegrationHarmonizer()

    provenance = {"system_id": "demo_system", "source": "main_demo", "timestamp": int(time.time())}

    try:
        # Test low drift (should pass)
        low_drift_result = harmonizer.reconcile(0.3, provenance)
        print(f"✓ Low drift handled: {low_drift_result['action']}")

        # Test high drift (requires proof)
        high_drift_provenance = {**provenance, "system_id": "drift_system"}
        high_drift_result = harmonizer.reconcile(0.9, high_drift_provenance)

        if high_drift_result["reconciled"]:
            print(f"✓ High drift reconciled: {high_drift_result['action']}")
        else:
            print(f"⚠ High drift quarantined: {high_drift_result['system_id']}")

        return True

    except Exception as e:
        print(f"✗ Drift reconciliation error: {e}")
        return False


def demo_proof_failure():
    """Demo 5: Show proof gate failure with DENY pattern"""
    print("\n=== Demo 5: Proof Gate Failure ===")

    nexus = LogosNexus()

    # Request that should be denied (contains DENY pattern)
    request = {"state": {"system": "DENY_active"}, "properties": {"safe": False}}

    provenance = {"user": "demo_user", "source": "failure_demo", "timestamp": int(time.time())}

    try:
        result = nexus.handle_request("DENY_action", request, provenance)
        if result["success"]:
            print(f"✗ Unexpected success: {result}")
            return False
        else:
            print("✓ Proof gate correctly denied request with DENY pattern")
            return True
    except (ProofGateError, KernelHashMismatchError):
        print("✓ Proof gate correctly denied request with DENY pattern")
        return True
    except Exception as e:
        print(f"✗ Unexpected error type: {e}")
        return False


def demo_trinity_gui():
    """Demo 6: LOGOS AGI Trinity Knot GUI - Simplified Dark Theme"""
    print("=== Demo 6: LOGOS AGI Trinity GUI ===")
    print("\nLaunching redesigned Trinity Knot interface...")
    print("Features:")
    print("  • Dark theme (#1a1a1a) with electric blue (#00bfff)")
    print("  • Trinity Knot icon with 4 animation states")
    print("  • Real-time WebSocket communication")
    print("  • Text query interface")
    print("  • Voice input toggle (push-to-talk)")
    print("  • File upload (10MB max)")
    print("  • Simplified interface (proof window removed)")

    import subprocess
    import webbrowser
    import time

    try:
        # Launch gui.py directly
        gui_path = os.path.join("..", "gui.py")

        print("\nStarting LOGOS AGI server...")
        server_process = subprocess.Popen(
            [sys.executable, gui_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            cwd=os.path.dirname(__file__)
        )

        # Wait for server startup
        time.sleep(4)

        # Check if server is running
        if server_process.poll() is None:
            print("✓ LOGOS AGI server started on http://localhost:5000")
            print("\nOpening browser...")
            time.sleep(1)
            webbrowser.open("http://localhost:5000")

            print("\n" + "=" * 50)
            print("LOGOS AGI Trinity Knot GUI is now running!")
            print("=" * 50)
            print("\nTest the interface:")
            print("  1. Ask: 'How does LOGOS think?'")
            print("  2. Click 🎤 for voice input")
            print("  3. Upload a file with 📁")
            print("\nTrinity Knot animations:")
            print("  • Deep blue pulse: Listening")
            print("  • Ice-to-white glow: Processing")
            print("  • Electric blue pulse: Responding")
            print("  • Spectrum fade: Stasis")
            print("\nPress Enter to stop the server...")

            input()

            # Stop server
            print("\nStopping LOGOS AGI server...")
            server_process.terminate()
            try:
                server_process.wait(timeout=5)
            except:
                server_process.kill()

            print("✓ Trinity GUI demo completed")
            return True
        else:
            print("✗ Failed to start LOGOS AGI server")
            stdout, stderr = server_process.communicate()
            print(f"Error: {stderr.decode()[:500]}")
            return False

    except FileNotFoundError as e:
        print(f"✗ Could not launch server: {e}")
        print("Ensure gui.py exists in the project root")
        return False
    except Exception as e:
        print(f"✗ Trinity GUI demo failed: {e}")
        try:
            server_process.terminate()
        except:
            pass
        return False


def show_audit_summary():
    """Show a summary of audit events"""
    print("\n=== Audit Log Summary ===")
    try:
        from persistence.persistence import AuditLog

        log = AuditLog()
        events = log.query_recent(limit=5)
        if events:
            print(f"Recent audit events ({len(events)}):")
            for event in events:
                action = event.get("action", "unknown")
                timestamp = event.get("timestamp", "unknown")
                status = event.get("status", "unknown")
                print(f"  • {timestamp}: {action} ({status})")
        else:
            print("No audit events found")
    except ImportError:
        print("⚠ Audit logging module not available")
    except Exception as e:
        print(f"⚠ Could not retrieve audit log: {e}")


def main():
    """Run all demo scenarios"""
    print("LOGOS Alignment Core Demo")
    print("=" * 50)
    print("Testing PXL proof gates, privative policies, and OBDC kernel")
    print()

    # Check if PXL server is running
    print("Checking PXL server availability...")
    try:
        from logos_core.pxl_client import PXLClient

        client = PXLClient("http://127.0.0.1:8088")
        health = client.health_check()
        if health.get("status") == "ok":
            print(f"✓ PXL server running (kernel: {health.get('kernel_hash', 'unknown')})")
        else:
            print("⚠ PXL server not responding - using stub behavior")
    except Exception as e:
        print(f"⚠ PXL server check failed: {e}")

    print()

    # Run demo scenarios
    demos = [
        demo_action_authorization,
        demo_plan_creation,
        demo_obdc_bijection,
        demo_drift_reconciliation,
        demo_proof_failure,
        demo_trinity_gui,  # Phase 2: Trinity Knot GUI
    ]

    results = []
    for demo in demos:
        try:
            success = demo()
            results.append(success)
        except Exception as e:
            print(f"✗ Demo failed with exception: {e}")
            results.append(False)
        print()

    # Show results summary
    print("=" * 50)
    print("Demo Results Summary:")
    passed = sum(results)
    total = len(results)
    print(f"Passed: {passed}/{total}")

    if passed == total:
        print("✓ All demos passed - Alignment core is working correctly")
    else:
        print("⚠ Some demos failed - Check PXL server and configuration")

    show_audit_summary()

    return passed == total


if __name__ == "__main__":
    success = main()
    sys.exit(0 if success else 1)
