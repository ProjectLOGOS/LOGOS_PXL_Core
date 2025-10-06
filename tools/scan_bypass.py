#!/usr/bin/env python3
"""
Bypass scanner - Detect potential bypasses of proof gates
"""

import pathlib
import re
import sys


def scan_for_bypasses():
    """Scan for potential proof gate bypasses"""
    print("Scanning for proof gate bypasses...")

    issues = []
    checked_files = 0

    # Patterns that indicate potential bypasses
    bypass_patterns = [
        (r"TODO.*bypass", "TODO bypass comment found"),
        (r"FIXME.*bypass", "FIXME bypass comment found"),
        (r"hack.*around.*proof", "Proof bypass hack detected"),
        (r"skip.*proof.*gate", "Proof gate skip detected"),
        (r"direct.*actuator", "Direct actuator access (should go through proof gate)"),
        (r"\.execute\(.*\).*#.*bypass", "Execute with bypass comment"),
    ]

    # Files that should contain proof gate calls
    proof_required_files = [
        "logos_core/unified_formalisms.py",
        "logos_core/archon_planner.py",
        "logos_core/logos_nexus.py",
        "obdc/kernel.py",
    ]

    for py_file in pathlib.Path(".").rglob("*.py"):
        # Skip test files and tools
        if "test" in str(py_file) or "tools" in str(py_file):
            continue

        try:
            content = py_file.read_text(encoding="utf-8", errors="ignore")
            checked_files += 1

            # Check for bypass patterns
            for pattern, message in bypass_patterns:
                matches = re.findall(pattern, content, re.IGNORECASE)
                if matches:
                    issues.append(f"{py_file}: {message} - {matches}")

            # Check that proof-required files actually call proof gates
            if str(py_file) in proof_required_files or any(
                req in str(py_file) for req in proof_required_files
            ):
                if "require_proof_token" not in content and "reference_monitor" not in content:
                    issues.append(f"{py_file}: Should contain proof gate calls but doesn't")

        except Exception as e:
            print(f"Warning: Could not scan {py_file}: {e}")

    print(f"Scanned {checked_files} Python files")

    if issues:
        print("\n⚠ Potential bypass issues found:")
        for issue in issues:
            print(f"  - {issue}")
        return False
    else:
        print("✓ No bypass issues detected")
        return True


def scan_for_todos():
    """Scan for TODO items that might indicate incomplete security"""
    print("\nScanning for security-related TODOs...")

    security_todos = []

    for py_file in pathlib.Path(".").rglob("*.py"):
        try:
            content = py_file.read_text(encoding="utf-8", errors="ignore")

            # Look for security-related TODOs
            lines = content.split("\n")
            for i, line in enumerate(lines, 1):
                if "TODO" in line.upper() and any(
                    keyword in line.lower()
                    for keyword in [
                        "security",
                        "auth",
                        "proof",
                        "bypass",
                        "hack",
                        "stub",
                        "placeholder",
                    ]
                ):
                    security_todos.append(f"{py_file}:{i}: {line.strip()}")

        except Exception:
            continue

    if security_todos:
        print("Security-related TODOs found:")
        for todo in security_todos[:10]:  # Limit output
            print(f"  - {todo}")
        if len(security_todos) > 10:
            print(f"  ... and {len(security_todos) - 10} more")
    else:
        print("✓ No security-related TODOs found")

    return len(security_todos) == 0


def main():
    """Run bypass scanning"""
    print("LOGOS Proof Gate Bypass Scanner")
    print("=" * 40)

    bypass_clean = scan_for_bypasses()
    todo_clean = scan_for_todos()

    print("\n" + "=" * 40)
    if bypass_clean and todo_clean:
        print("✓ Scan complete - no bypass issues detected")
        return 0
    else:
        print("⚠ Scan complete - potential issues found")
        return 1


if __name__ == "__main__":
    sys.exit(main())
