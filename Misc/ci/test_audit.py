#!/usr/bin/env python3
"""Test script for audit log validation"""
import os
import sys

sys.path.append("..")

from persistence.persistence import AuditLog

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
