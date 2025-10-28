#!/usr/bin/env python3
"""
LOGOS System Monitor
Command-line monitoring and diagnostic tool for LOGOS AGI system
"""

import json
import time
import sys
from pathlib import Path

# Add LOGOS to path
sys.path.insert(0, str(Path(__file__).parent / "LOGOS_V2"))

try:
    from LOGOS_V2.entry import get_logos_core, initialize_logos_core
    LOGOS_AVAILABLE = True
except ImportError as e:
    print(f"LOGOS not available: {e}")
    LOGOS_AVAILABLE = False

def get_detailed_status():
    """Get comprehensive system status"""
    if not LOGOS_AVAILABLE:
        return {"error": "LOGOS system not available"}

    try:
        core = get_logos_core()

        # Basic status
        status = core.get_system_status()

        # Safety system details
        safety_status = {
            "system_halted": status.get("integrity_safeguard", {}).get("system_halted", True),
            "permanent_lockout": status.get("integrity_safeguard", {}).get("permanent_lockout", False),
            "active_violations": status.get("integrity_safeguard", {}).get("active_violations", 0),
            "violation_types": status.get("integrity_safeguard", {}).get("violation_states", [])
        }

        # IEL system details
        iel_status = status.get("iel", {})
        iel_details = {
            "available": iel_status.get("iel_available", False),
            "registry_loaded": iel_status.get("registry_loaded", False),
            "active_domains": iel_status.get("active_domains", []),
            "domain_instances": iel_status.get("domain_instances", 0),
            "available_domains": iel_status.get("available_domains", [])
        }

        # Reference monitor status
        monitor_status = status.get("monitor", {})

        return {
            "timestamp": time.time(),
            "system_health": "GOOD" if not safety_status["system_halted"] else "CRITICAL",
            "safety_system": safety_status,
            "iel_system": iel_details,
            "reference_monitor": monitor_status,
            "raw_status": status
        }

    except Exception as e:
        return {"error": f"Failed to get status: {str(e)}"}

def print_status_report():
    """Print formatted status report"""
    status = get_detailed_status()

    if "error" in status:
        print(f"❌ ERROR: {status['error']}")
        return

    print("🤖 LOGOS AGI System Status Report")
    print("=" * 50)
    print(f"Timestamp: {time.strftime('%Y-%m-%d %H:%M:%S', time.localtime(status['timestamp']))}")
    print(f"System Health: {status['system_health']}")
    print()

    # Safety System
    safety = status['safety_system']
    print("🛡️ Safety System:")
    print(f"  Status: {'🟢 ACTIVE' if not safety['system_halted'] else '🔴 HALTED'}")
    print(f"  Permanent Lockout: {'Yes' if safety['permanent_lockout'] else 'No'}")
    print(f"  Active Violations: {safety['active_violations']}")
    if safety['violation_types']:
        print(f"  Violation Types: {', '.join(safety['violation_types'])}")
    print()

    # IEL System
    iel = status['iel_system']
    print("🧠 IEL System:")
    print(f"  Available: {'Yes' if iel['available'] else 'No'}")
    print(f"  Registry Loaded: {'Yes' if iel['registry_loaded'] else 'No'}")
    print(f"  Active Domains: {len(iel['active_domains'])}")
    if iel['active_domains']:
        print(f"    Domains: {', '.join(iel['active_domains'])}")
    print(f"  Domain Instances: {iel['domain_instances']}")
    print(f"  Available Domains: {len(iel['available_domains'])}")
    print()

    # Reference Monitor
    monitor = status['reference_monitor']
    if monitor:
        print("👁️ Reference Monitor:")
        for key, value in monitor.items():
            print(f"  {key}: {value}")
        print()

def export_json_report(filename=None):
    """Export status as JSON"""
    status = get_detailed_status()

    if filename:
        with open(filename, 'w') as f:
            json.dump(status, f, indent=2)
        print(f"Report exported to: {filename}")
    else:
        print(json.dumps(status, indent=2))

def main():
    import argparse

    parser = argparse.ArgumentParser(description="LOGOS System Monitor")
    parser.add_argument("--json", help="Export as JSON to file")
    parser.add_argument("--watch", action="store_true", help="Continuous monitoring mode")
    parser.add_argument("--interval", type=int, default=5, help="Watch interval in seconds")

    args = parser.parse_args()

    if args.json:
        export_json_report(args.json)
    elif args.watch:
        print("Starting continuous monitoring (Ctrl+C to stop)...")
        try:
            while True:
                print("\033c", end="")  # Clear screen
                print_status_report()
                time.sleep(args.interval)
        except KeyboardInterrupt:
            print("\nMonitoring stopped.")
    else:
        print_status_report()

if __name__ == "__main__":
    main()