#!/usr/bin/env python3
"""Simple test script to verify the enhanced tool router is working."""

import requests
import time

def test_metrics():
    """Test the Prometheus metrics endpoint."""
    try:
        response = requests.get("http://localhost:8000/metrics", timeout=5)
        print(f"Metrics endpoint status: {response.status_code}")
        if response.status_code == 200:
            content = response.text
            print("✅ Metrics endpoint working!")
            print("\nSample metrics:")
            lines = content.split('\n')[:20]  # First 20 lines
            for line in lines:
                if line.strip() and not line.startswith('#'):
                    print(f"  {line}")
            return True
        else:
            print(f"❌ Metrics endpoint returned {response.status_code}")
            return False
    except requests.exceptions.RequestException as e:
        print(f"❌ Failed to connect to metrics endpoint: {e}")
        return False

def test_health():
    """Test the health endpoint."""
    try:
        response = requests.get("http://localhost:8000/health", timeout=5)
        print(f"Health endpoint status: {response.status_code}")
        if response.status_code == 200:
            print("✅ Health endpoint working!")
            print(f"  Response: {response.json()}")
            return True
        else:
            print(f"❌ Health endpoint returned {response.status_code}")
            return False
    except requests.exceptions.RequestException as e:
        print(f"❌ Failed to connect to health endpoint: {e}")
        return False

if __name__ == "__main__":
    print("Testing Enhanced LOGOS Tool Router v2.0.0")
    print("==========================================")
    
    print("\n1. Testing health endpoint...")
    health_ok = test_health()
    
    print("\n2. Testing Prometheus metrics endpoint...")
    metrics_ok = test_metrics()
    
    if health_ok and metrics_ok:
        print("\n✅ All tests passed! Enhanced tool router is working correctly.")
    else:
        print("\n❌ Some tests failed. Check the service status.")