#!/usr/bin/env python3
"""Test script for audit log validation"""
import os
import sys

# Add the parent directory to the path to find the persistence module
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

try:
    from persistence import AuditLog
except ImportError:
    print("Error: persistence module not found")
    print("Make sure the persistence module is installed or in the correct location")
    sys.exit(1)

# Create test audit directory
os.makedirs("../audit", exist_ok=True)

# Test audit log creation
audit = AuditLog("../audit/test.jsonl")
record = {
    "obligation": "BOX(test)",
    "provenance": {"test": True},
    "decision": "ALLOW",
    "proof": {"id": "test", "kernel_hash": "TEST"},
}
audit.append(record)

# Validate structure
stats = audit.get_stats()
if stats["total_records"] != 1:
    print("Audit test failed")
    sys.exit(1)
print("Audit validation passed")
