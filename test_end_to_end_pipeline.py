#!/usr/bin/env python3
"""
End-to-End Pipeline Integration Test

Tests the complete Phase 1→2 Bridge: Passive Loop → IEL Generation pipeline
validating each step of the autonomous reasoning cycle.
"""

import os
import json
import subprocess
import tempfile
from pathlib import Path


def test_end_to_end_pipeline():
    """Test complete end-to-end pipeline execution"""
    print("🔧 Testing End-to-End Pipeline...")
    
    # Step 1: Verify daemon can run
    print("  ✓ Step 1: Testing daemon execution...")
    result = subprocess.run([
        "python", "-m", "logos_core.daemon.logos_daemon", 
        "--once", "--emit-gaps", "--out", "metrics/test_status.jsonl"
    ], capture_output=True, text=True, cwd=os.getcwd())
    
    assert result.returncode == 0, f"Daemon failed: {result.stderr}"
    assert Path("metrics/test_status.jsonl").exists(), "Gap telemetry not generated"
    
    # Step 2: Verify gap artifacts exist
    print("  ✓ Step 2: Checking gap detection...")
    with open("metrics/test_status.jsonl", 'r') as f:
        telemetry = [json.loads(line) for line in f]
    
    assert len(telemetry) > 0, "No telemetry generated"
    gap_events = [t for t in telemetry if t.get('event_type') in ['gap_detected', 'reasoning_gap_detected']]
    assert len(gap_events) > 0, "No reasoning gaps detected"
    
    # Step 3: Verify IEL generation
    print("  ✓ Step 3: Testing IEL generation...")
    result = subprocess.run([
        "python", "-m", "logos_core.meta_reasoning.iel_generator",
        "--from-log", "metrics/test_status.jsonl",
        "--out", "build/test_candidate.v"
    ], capture_output=True, text=True, cwd=os.getcwd())
    
    assert result.returncode == 0, f"IEL generation failed: {result.stderr}"
    assert Path("build/test_candidate.v").exists(), "IEL candidate not generated"
    
    # Step 4: Verify signing
    print("  ✓ Step 4: Testing cryptographic signing...")
    result = subprocess.run([
        "python", "-m", "logos_core.governance.iel_signer",
        "--sign", "build/test_candidate.v",
        "--key", "keys/iel_signing.pem",
        "--out", "build/test_candidate.sig"
    ], capture_output=True, text=True, cwd=os.getcwd())
    
    assert result.returncode == 0, f"IEL signing failed: {result.stderr}"
    assert Path("build/test_candidate.sig").exists(), "Signature not generated"
    
    # Step 5: Verify registry integration
    print("  ✓ Step 5: Testing registry integration...")
    result = subprocess.run([
        "python", "-m", "logos_core.meta_reasoning.iel_registry",
        "--add", "build/test_candidate.v",
        "--sig", "build/test_candidate.sig",
        "--registry", "registry/test_registry.json"
    ], capture_output=True, text=True, cwd=os.getcwd())
    
    assert result.returncode == 0, f"Registry registration failed: {result.stderr}"
    
    # Step 6: Verify registry listing
    print("  ✓ Step 6: Testing registry queries...")
    result = subprocess.run([
        "python", "-m", "logos_core.meta_reasoning.iel_registry",
        "--list", "--registry", "registry/test_registry.json"
    ], capture_output=True, text=True, cwd=os.getcwd())
    
    assert result.returncode == 0, f"Registry listing failed: {result.stderr}"
    assert "Registry contains" in result.stdout, "Registry listing malformed"
    
    # Cleanup test artifacts
    test_files = [
        "metrics/test_status.jsonl",
        "build/test_candidate.v", 
        "build/test_candidate.sig",
        "registry/test_registry.json",
        "registry/test_registry.db"
    ]
    
    for test_file in test_files:
        if Path(test_file).exists():
            Path(test_file).unlink()
    
    print("🎯 End-to-End Pipeline Test: PASSED")
    return True


def test_component_interfaces():
    """Test that all components have proper CLI interfaces"""
    print("🔧 Testing Component Interfaces...")
    
    components = [
        "logos_core.daemon.logos_daemon",
        "logos_core.meta_reasoning.iel_generator", 
        "logos_core.governance.iel_signer",
        "logos_core.meta_reasoning.iel_registry"
    ]
    
    for component in components:
        result = subprocess.run([
            "python", "-m", component, "--help"
        ], capture_output=True, text=True, cwd=os.getcwd())
        
        assert result.returncode == 0, f"Component {component} CLI broken"
        assert "usage:" in result.stdout.lower() or "Usage:" in result.stdout, f"Component {component} help malformed"
    
    print("🎯 Component Interface Test: PASSED")
    return True


def test_artifacts_validation():
    """Test that generated artifacts have proper format"""
    print("🔧 Testing Artifact Validation...")
    
    # Check existing artifacts
    artifacts = [
        ("metrics/agi_status.jsonl", "telemetry"),
        ("build/candidate_iel.v", "coq"),
        ("build/candidate_iel.sig", "signature"),
        ("registry/iel_registry.db", "database")
    ]
    
    for artifact_path, artifact_type in artifacts:
        if Path(artifact_path).exists():
            print(f"  ✓ Found {artifact_type}: {artifact_path}")
            
            if artifact_type == "signature":
                with open(artifact_path, 'r') as f:
                    sig_data = json.load(f)
                assert "signature" in sig_data, f"Invalid signature format in {artifact_path}"
                assert "algorithm" in sig_data, f"Missing algorithm in {artifact_path}"
            
            elif artifact_type == "coq":
                with open(artifact_path, 'r') as f:
                    content = f.read()
                assert "Lemma" in content, f"Invalid IEL format in {artifact_path}"
    
    print("🎯 Artifact Validation Test: PASSED")
    return True


if __name__ == '__main__':
    try:
        test_component_interfaces()
        test_artifacts_validation()
        test_end_to_end_pipeline()
        print("\n🎉 ALL TESTS PASSED - Pipeline is fully operational!")
    except AssertionError as e:
        print(f"\n❌ TEST FAILED: {e}")
        exit(1)
    except Exception as e:
        print(f"\n💥 UNEXPECTED ERROR: {e}")
        exit(1)