#!/usr/bin/env python3
"""Test script for proof endpoint validation"""

import json

try:
    with open("/tmp/prove.json") as f:
        result = json.load(f)

    assert "kernel_hash" in result, "Missing kernel_hash"
    assert "id" in result, "Missing proof id"
    print("Proof endpoint test passed")
except Exception as e:
    print(f"Proof endpoint test failed: {e}")
    exit(1)
