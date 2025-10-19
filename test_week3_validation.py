#!/usr/bin/env python3
"""
test_week3_validation.py - Comprehensive validation for Week 3 objectives
Tests HMAC authentication, performance monitoring, and cache optimization
"""

import json
import time
import hashlib
import hmac
import requests
import threading
import statistics
from datetime import datetime, timezone
from concurrent.futures import ThreadPoolExecutor, as_completed


class Week3Validator:
    """Comprehensive validator for Week 3 Security Hardening and Performance Optimization"""

    def __init__(self, base_url="http://localhost:5000", hmac_key="test_secret_key"):
        self.base_url = base_url
        self.hmac_key = hmac_key.encode('utf-8')
        self.results = {
            "hmac_auth": {"passed": False, "details": {}},
            "performance": {"passed": False, "details": {}},
            "cache_optimization": {"passed": False, "details": {}},
            "overall": {"passed": False, "summary": ""}
        }

    def generate_hmac_headers(self, body=""):
        """Generate HMAC authentication headers"""
        timestamp = str(int(time.time()))
        nonce = hashlib.sha256(f"{timestamp}{time.time()}".encode()).hexdigest()[:16]

        # Create signature data
        signature_data = f"{timestamp}:{nonce}:{body}"
        signature = hmac.new(
            self.hmac_key,
            signature_data.encode('utf-8'),
            hashlib.sha256
        ).hexdigest()

        return {
            "X-Timestamp": timestamp,
            "X-Nonce": nonce,
            "X-Signature": signature
        }

    def test_hmac_authentication(self):
        """Test HMAC authentication functionality"""
        print("🔐 Testing HMAC Authentication...")

        test_goal = '{"goal": "BOX(A -> A)"}'

        # Test 1: Valid HMAC request
        try:
            headers = self.generate_hmac_headers(test_goal)
            headers["Content-Type"] = "application/json"

            response = requests.post(
                f"{self.base_url}/prove",
                headers=headers,
                data=test_goal,
                timeout=10
            )

            if response.status_code == 200:
                self.results["hmac_auth"]["details"]["valid_auth"] = "PASSED"
                print("  ✅ Valid HMAC authentication: PASSED")
            else:
                self.results["hmac_auth"]["details"]["valid_auth"] = f"FAILED - {response.status_code}"
                print(f"  ❌ Valid HMAC authentication: FAILED - {response.status_code}")

        except Exception as e:
            self.results["hmac_auth"]["details"]["valid_auth"] = f"ERROR - {str(e)}"
            print(f"  ❌ Valid HMAC authentication: ERROR - {str(e)}")

        # Test 2: Invalid signature
        try:
            headers = self.generate_hmac_headers(test_goal)
            headers["X-Signature"] = "invalid_signature"
            headers["Content-Type"] = "application/json"

            response = requests.post(
                f"{self.base_url}/prove",
                headers=headers,
                data=test_goal,
                timeout=10
            )

            if response.status_code == 401:
                self.results["hmac_auth"]["details"]["invalid_signature"] = "PASSED"
                print("  ✅ Invalid signature rejection: PASSED")
            else:
                self.results["hmac_auth"]["details"]["invalid_signature"] = f"FAILED - Expected 401, got {response.status_code}"
                print(f"  ❌ Invalid signature rejection: FAILED - Expected 401, got {response.status_code}")

        except Exception as e:
            self.results["hmac_auth"]["details"]["invalid_signature"] = f"ERROR - {str(e)}"
            print(f"  ❌ Invalid signature rejection: ERROR - {str(e)}")

        # Test 3: Timestamp replay attack protection
        try:
            old_timestamp = str(int(time.time()) - 120)  # 2 minutes ago
            nonce = hashlib.sha256(f"{old_timestamp}{time.time()}".encode()).hexdigest()[:16]

            signature_data = f"{old_timestamp}:{nonce}:{test_goal}"
            signature = hmac.new(
                self.hmac_key,
                signature_data.encode('utf-8'),
                hashlib.sha256
            ).hexdigest()

            headers = {
                "X-Timestamp": old_timestamp,
                "X-Nonce": nonce,
                "X-Signature": signature,
                "Content-Type": "application/json"
            }

            response = requests.post(
                f"{self.base_url}/prove",
                headers=headers,
                data=test_goal,
                timeout=10
            )

            if response.status_code == 401:
                self.results["hmac_auth"]["details"]["replay_protection"] = "PASSED"
                print("  ✅ Timestamp replay protection: PASSED")
            else:
                self.results["hmac_auth"]["details"]["replay_protection"] = f"FAILED - Expected 401, got {response.status_code}"
                print(f"  ❌ Timestamp replay protection: FAILED - Expected 401, got {response.status_code}")

        except Exception as e:
            self.results["hmac_auth"]["details"]["replay_protection"] = f"ERROR - {str(e)}"
            print(f"  ❌ Timestamp replay protection: ERROR - {str(e)}")

        # Determine overall HMAC auth result
        passed_tests = sum(1 for test in self.results["hmac_auth"]["details"].values() if "PASSED" in str(test))
        total_tests = len(self.results["hmac_auth"]["details"])
        self.results["hmac_auth"]["passed"] = passed_tests == total_tests

        print(f"  📊 HMAC Authentication: {passed_tests}/{total_tests} tests passed")

    def test_performance_monitoring(self):
        """Test performance monitoring capabilities"""
        print("⚡ Testing Performance Monitoring...")

        # Test concurrent load for P95 latency measurement
        test_goals = [
            "BOX(A -> A)",
            "BOX(A /\\ B -> A)",
            "BOX(A -> A \\/ B)",
            "BOX((A -> B) -> ((B -> C) -> (A -> C)))",
            "BOX(A /\\ B -> B /\\ A)"
        ]

        latencies = []
        errors = 0

        def send_request(goal):
            try:
                start_time = time.time()

                body = json.dumps({"goal": goal})
                headers = self.generate_hmac_headers(body)
                headers["Content-Type"] = "application/json"

                response = requests.post(
                    f"{self.base_url}/prove",
                    headers=headers,
                    data=body,
                    timeout=10
                )

                latency = (time.time() - start_time) * 1000  # Convert to milliseconds

                if response.status_code == 200:
                    return latency, None
                else:
                    return latency, f"HTTP {response.status_code}"

            except Exception as e:
                return 5000, str(e)  # High latency for errors

        # Concurrent load test
        print("  🔄 Running concurrent load test (100 requests)...")
        with ThreadPoolExecutor(max_workers=10) as executor:
            futures = []

            for i in range(100):
                goal = test_goals[i % len(test_goals)]
                futures.append(executor.submit(send_request, goal))

            for future in as_completed(futures):
                latency, error = future.result()
                latencies.append(latency)
                if error:
                    errors += 1

        # Calculate statistics
        if latencies:
            p50 = statistics.median(latencies)
            p90 = statistics.quantiles(latencies, n=10)[8]  # 90th percentile
            p95 = statistics.quantiles(latencies, n=20)[18]  # 95th percentile
            p99 = statistics.quantiles(latencies, n=100)[98]  # 99th percentile

            self.results["performance"]["details"] = {
                "total_requests": len(latencies),
                "errors": errors,
                "p50_latency": round(p50, 2),
                "p90_latency": round(p90, 2),
                "p95_latency": round(p95, 2),
                "p99_latency": round(p99, 2),
                "p95_target_met": p95 < 300
            }

            print(f"    📈 P50: {p50:.1f}ms, P90: {p90:.1f}ms, P95: {p95:.1f}ms, P99: {p99:.1f}ms")
            print(f"    🎯 P95 < 300ms target: {'✅ MET' if p95 < 300 else '❌ MISSED'}")
            print(f"    ⚠️  Errors: {errors}/{len(latencies)}")

            self.results["performance"]["passed"] = p95 < 300 and errors < len(latencies) * 0.05
        else:
            self.results["performance"]["passed"] = False
            print("  ❌ No latency data collected")

    def test_cache_optimization(self):
        """Test cache optimization and hit rate"""
        print("🚀 Testing Cache Optimization...")

        # Warm up cache with repeated requests
        test_goal = "BOX(A -> A)"
        body = json.dumps({"goal": test_goal})
        headers = self.generate_hmac_headers(body)
        headers["Content-Type"] = "application/json"

        # Send initial requests to populate cache
        print("  🔥 Warming up cache...")
        for _ in range(10):
            requests.post(f"{self.base_url}/prove", headers=headers, data=body, timeout=10)
            time.sleep(0.1)

        # Get initial cache stats
        try:
            health_response = requests.get(f"{self.base_url}/health", timeout=10)
            initial_stats = health_response.json().get("cache_stats", {})
        except:
            initial_stats = {}

        # Send more requests to test cache hits
        print("  📊 Testing cache hit performance...")
        cache_test_requests = 50

        for _ in range(cache_test_requests):
            requests.post(f"{self.base_url}/prove", headers=headers, data=body, timeout=10)

        # Get final cache stats
        try:
            health_response = requests.get(f"{self.base_url}/health", timeout=10)
            final_stats = health_response.json().get("cache_stats", {})

            hit_rate = final_stats.get("hit_rate", 0) * 100
            cache_hits = final_stats.get("cache_hits", 0)
            cache_misses = final_stats.get("cache_misses", 0)
            prefetch_hits = final_stats.get("prefetch_hits", 0)

            self.results["cache_optimization"]["details"] = {
                "hit_rate_percent": round(hit_rate, 1),
                "cache_hits": cache_hits,
                "cache_misses": cache_misses,
                "prefetch_hits": prefetch_hits,
                "hit_rate_target_met": hit_rate >= 85
            }

            print(f"    📊 Cache Hit Rate: {hit_rate:.1f}%")
            print(f"    🎯 ≥85% target: {'✅ MET' if hit_rate >= 85 else '❌ MISSED'}")
            print(f"    🔄 Cache Hits: {cache_hits}, Misses: {cache_misses}")
            print(f"    ⚡ Prefetch Hits: {prefetch_hits}")

            self.results["cache_optimization"]["passed"] = hit_rate >= 85

        except Exception as e:
            print(f"  ❌ Could not retrieve cache statistics: {e}")
            self.results["cache_optimization"]["passed"] = False

    def run_full_validation(self):
        """Run complete Week 3 validation suite"""
        print("=" * 60)
        print("🚀 WEEK 3 VALIDATION: Security Hardening & Performance Optimization")
        print("=" * 60)

        start_time = time.time()

        # Test server availability
        try:
            response = requests.get(f"{self.base_url}/health", timeout=10)
            if response.status_code != 200:
                print(f"❌ Server not available at {self.base_url}")
                return False
            print(f"✅ Server health check passed")
        except Exception as e:
            print(f"❌ Server connection failed: {e}")
            return False

        # Run all tests
        self.test_hmac_authentication()
        print()
        self.test_performance_monitoring()
        print()
        self.test_cache_optimization()

        # Overall validation result
        overall_passed = (
            self.results["hmac_auth"]["passed"] and
            self.results["performance"]["passed"] and
            self.results["cache_optimization"]["passed"]
        )

        self.results["overall"]["passed"] = overall_passed

        # Summary report
        print("\n" + "=" * 60)
        print("📋 WEEK 3 VALIDATION SUMMARY")
        print("=" * 60)

        validation_time = time.time() - start_time

        auth_status = "✅ PASS" if self.results["hmac_auth"]["passed"] else "❌ FAIL"
        perf_status = "✅ PASS" if self.results["performance"]["passed"] else "❌ FAIL"
        cache_status = "✅ PASS" if self.results["cache_optimization"]["passed"] else "❌ FAIL"
        overall_status = "✅ COMPLETE" if overall_passed else "❌ INCOMPLETE"

        print(f"🔐 HMAC Authentication:     {auth_status}")
        print(f"⚡ Performance Monitoring:  {perf_status}")
        print(f"🚀 Cache Optimization:      {cache_status}")
        print(f"📊 Overall Status:          {overall_status}")
        print(f"⏱️  Validation Time:         {validation_time:.1f}s")

        if overall_passed:
            print("\n🎉 WEEK 3 OBJECTIVES ACHIEVED!")
            print("✅ Cryptographic verification strengthened")
            print("✅ P95 latency < 300ms target met")
            print("✅ Cache hit rate ≥ 85% achieved")
            print("✅ Security hardening and performance optimization complete")
            self.results["overall"]["summary"] = "All Week 3 objectives successfully achieved"
        else:
            print("\n💥 WEEK 3 VALIDATION FAILED")
            print("❌ Some objectives not met - review implementation")
            self.results["overall"]["summary"] = "Week 3 objectives not fully achieved"

        print("=" * 60)

        return overall_passed

    def save_results(self, filename="week3_validation_results.json"):
        """Save validation results to JSON file"""
        results_with_metadata = {
            "validation_timestamp": datetime.now(timezone.utc).isoformat(),
            "week3_objectives": [
                "HMAC-SHA256 authentication with anti-replay protection",
                "Performance monitoring with P95 < 300ms",
                "Cache optimization with ≥85% hit rate",
                "CI benchmark integration",
                "Security hardening validation"
            ],
            "results": self.results
        }

        with open(filename, 'w') as f:
            json.dump(results_with_metadata, f, indent=2)

        print(f"📄 Results saved to {filename}")


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Week 3 Validation Suite")
    parser.add_argument("--url", default="http://localhost:5000", help="Server URL")
    parser.add_argument("--hmac-key", default="test_secret_key", help="HMAC secret key")
    parser.add_argument("--save-results", action="store_true", help="Save results to JSON")

    args = parser.parse_args()

    validator = Week3Validator(base_url=args.url, hmac_key=args.hmac_key)
    success = validator.run_full_validation()

    if args.save_results:
        validator.save_results()

    exit(0 if success else 1)
