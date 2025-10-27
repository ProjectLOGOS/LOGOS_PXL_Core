#!/usr/bin/env python3
"""
Simple Manual Test Script for LOGOS Services
"""
import requests
import time
import json

def test_service(name, url, expected_status=200):
    """Test a single service endpoint"""
    try:
        print(f"Testing {name} at {url}...")
        response = requests.get(url, timeout=5)
        
        if response.status_code == expected_status:
            print(f"✅ {name}: SUCCESS (Status: {response.status_code})")
            try:
                data = response.json()
                print(f"   Response: {json.dumps(data, indent=2)}")
            except:
                print(f"   Response: {response.text[:100]}...")
            return True
        else:
            print(f"❌ {name}: FAILED (Status: {response.status_code})")
            print(f"   Response: {response.text[:200]}")
            return False
            
    except requests.exceptions.ConnectionError:
        print(f"❌ {name}: CONNECTION FAILED - Service not running")
        return False
    except Exception as e:
        print(f"❌ {name}: ERROR - {str(e)}")
        return False

def test_post_endpoint(name, url, data, expected_status=200):
    """Test a POST endpoint"""
    try:
        print(f"Testing {name} POST at {url}...")
        response = requests.post(url, json=data, timeout=5)
        
        if response.status_code == expected_status:
            print(f"✅ {name}: SUCCESS (Status: {response.status_code})")
            try:
                response_data = response.json()
                print(f"   Response: {json.dumps(response_data, indent=2)}")
            except:
                print(f"   Response: {response.text[:100]}...")
            return True
        else:
            print(f"❌ {name}: FAILED (Status: {response.status_code})")
            print(f"   Response: {response.text[:200]}")
            return False
            
    except requests.exceptions.ConnectionError:
        print(f"❌ {name}: CONNECTION FAILED - Service not running")
        return False
    except Exception as e:
        print(f"❌ {name}: ERROR - {str(e)}")
        return False

def main():
    print("🚀 LOGOS AGI SYSTEM - MANUAL SERVICE TEST")
    print("=" * 50)
    
    # Test each service
    services = [
        ("LOGOS API Health", "http://localhost:8090/health"),
        ("Tool Router Health", "http://localhost:8000/health"),
        ("Tool Router Metrics", "http://localhost:8000/metrics"),
        ("Interactive Chat", "http://localhost:8080/"),
    ]
    
    results = []
    for name, url in services:
        result = test_service(name, url)
        results.append((name, result))
        time.sleep(1)
    
    print("\n" + "=" * 50)
    print("POST ENDPOINT TESTS")
    print("=" * 50)
    
    # Test POST endpoints
    post_tests = [
        ("LOGOS API Authorization", "http://localhost:8090/authorize_action", {
            "action": "test_action",
            "state": {"test": "data"}
        }),
        ("Tool Router Chat", "http://localhost:8000/chat", {
            "message": "Hello, test message",
            "user_id": "test_user"
        }),
    ]
    
    for name, url, data in post_tests:
        result = test_post_endpoint(name, url, data)
        results.append((name, result))
        time.sleep(1)
    
    print("\n" + "=" * 50) 
    print("TEST SUMMARY")
    print("=" * 50)
    
    passed = sum(1 for _, result in results if result)
    total = len(results)
    
    for name, result in results:
        status = "✅ PASS" if result else "❌ FAIL"
        print(f"{status} {name}")
    
    print(f"\nResults: {passed}/{total} tests passed")
    
    if passed == total:
        print("🎉 ALL SERVICES OPERATIONAL!")
    else:
        print("⚠️  Some services need attention")

if __name__ == "__main__":
    main()