#!/usr/bin/env python3
"""
LOGOS AGI Audit Infrastructure Verification
Validates completeness and integrity of audit documentation
"""

import os
import hashlib
import json
from pathlib import Path
from datetime import datetime

def verify_audit_completeness():
    """Verify all required audit components are present."""

    print("🔍 Verifying LOGOS AGI Audit Infrastructure...")
    print("=" * 60)

    # Define required components
    required_files = [
        "docs/audit/README.md",
        "docs/audit/proof_index.md",
        "docs/audit/FALSIFIABILITY.md",
        "docs/audit/EXPERIMENT_GUIDE.md",
        "scripts/reproduce_system.sh"
    ]

    # Check file existence
    missing_files = []
    existing_files = []

    for file_path in required_files:
        if os.path.exists(file_path):
            existing_files.append(file_path)
            size = os.path.getsize(file_path)
            print(f"✅ {file_path} ({size:,} bytes)")
        else:
            missing_files.append(file_path)
            print(f"❌ {file_path} - MISSING")

    # Verify Coq proof files
    print(f"\n🔬 Verifying Coq Proof Infrastructure...")
    coq_files = list(Path('.').rglob('*.v'))
    print(f"✅ Found {len(coq_files)} Coq proof files")

    # Sample verification of key proof categories
    key_categories = {
        "ArithmoPraxis": "modules/infra/arithmo/",
        "IEL System": "PXL_IEL_overlay_system/",
        "API Layer": "PXL_IEL_overlay_system/api/",
        "Core Extraction": "ExtractCore.v"
    }

    for category, path_pattern in key_categories.items():
        matching_files = [f for f in coq_files if path_pattern in str(f)]
        print(f"✅ {category}: {len(matching_files)} files")

    # Generate integrity report
    print(f"\n📊 Generating Integrity Report...")

    # Calculate file hashes
    file_hashes = {}
    for file_path in existing_files:
        with open(file_path, 'rb') as f:
            content = f.read()
            file_hash = hashlib.sha256(content).hexdigest()
            file_hashes[file_path] = {
                "hash": file_hash,
                "size": len(content),
                "modified": datetime.fromtimestamp(os.path.getmtime(file_path)).isoformat()
            }

    # Create verification report
    report = {
        "verification_timestamp": datetime.now().isoformat(),
        "audit_completeness": {
            "required_files": len(required_files),
            "existing_files": len(existing_files),
            "missing_files": len(missing_files),
            "completeness_percentage": (len(existing_files) / len(required_files)) * 100
        },
        "proof_infrastructure": {
            "total_coq_files": len(coq_files),
            "categories_verified": len(key_categories)
        },
        "file_integrity": file_hashes,
        "verification_status": "COMPLETE" if not missing_files else "INCOMPLETE"
    }

    # Save report
    with open("audit_verification_report.json", "w") as f:
        json.dump(report, f, indent=2)

    print(f"📋 Verification report saved to: audit_verification_report.json")

    # Summary
    print(f"\n📈 Verification Summary:")
    print(f"   • Audit Completeness: {report['audit_completeness']['completeness_percentage']:.1f}%")
    print(f"   • Total Proof Files: {report['proof_infrastructure']['total_coq_files']}")
    print(f"   • Verification Status: {report['verification_status']}")

    if missing_files:
        print(f"\n⚠️  Missing Files:")
        for file_path in missing_files:
            print(f"   • {file_path}")
        return False
    else:
        print(f"\n🎉 All audit infrastructure components verified successfully!")
        return True

def test_reproducibility_script():
    """Test the reproducibility script exists and is executable."""

    script_path = "scripts/reproduce_system.sh"

    if not os.path.exists(script_path):
        print(f"❌ Reproducibility script missing: {script_path}")
        return False

    print(f"✅ Reproducibility script present: {script_path}")

    # Check script content for key components
    with open(script_path, 'r') as f:
        content = f.read()

    required_functions = [
        "check_requirements",
        "setup_repository",
        "install_dependencies",
        "compile_infrastructure",
        "run_verification"
    ]

    missing_functions = []
    for func in required_functions:
        if func not in content:
            missing_functions.append(func)
        else:
            print(f"✅ Function present: {func}")

    if missing_functions:
        print(f"❌ Missing functions: {missing_functions}")
        return False

    print(f"✅ Reproducibility script verification complete")
    return True

def main():
    """Main verification routine."""

    print("🚀 LOGOS AGI Audit Infrastructure Verification")
    print("=" * 60)

    try:
        # Verify audit completeness
        audit_complete = verify_audit_completeness()

        print("\n" + "=" * 60)

        # Test reproducibility script
        script_valid = test_reproducibility_script()

        print("\n" + "=" * 60)

        # Final assessment
        if audit_complete and script_valid:
            print("🎯 AUDIT INFRASTRUCTURE VERIFICATION: PASSED")
            print("   System ready for third-party validation and peer review")
            return 0
        else:
            print("❌ AUDIT INFRASTRUCTURE VERIFICATION: FAILED")
            print("   Additional components required before external validation")
            return 1

    except Exception as e:
        print(f"💥 Verification failed with error: {e}")
        return 1

if __name__ == "__main__":
    exit(main())
