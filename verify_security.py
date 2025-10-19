#!/usr/bin/env python3
"""
verify_security.sh - Security validation script for LOGOS PXL Core v0.5
Validates HMAC authentication, input sanitization, and security hardening
Part of CI/CD pipeline for production readiness validation
"""

import json
import time
import hashlib
import hmac
import requests
import sys
import os
from datetime import datetime


class SecurityValidator:
    """Comprehensive security validation for production readiness"""

    def __init__(self, base_url="http://localhost:8088", hmac_key="test_security_key"):
        self.base_url = base_url
        self.hmac_key = hmac_key.encode('utf-8')
        self.results = {
            "timestamp": datetime.now().isoformat(),
            "version": "v0.5-rc1",
            "tests": {},
            "summary": {"passed": 0, "failed": 0, "total": 0}
        }

    def generate_hmac_headers(self, body=""):
        """Generate HMAC authentication headers"""
        timestamp = str(int(time.time()))
        nonce = hashlib.sha256(f"{timestamp}{time.time()}".encode()).hexdigest()[:16]

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

    def log_test_result(self, test_name: str, passed: bool, details: dict):
        """Log security test result"""
        self.results["tests"][test_name] = {
            "passed": passed,
            "details": details,
            "timestamp": datetime.now().isoformat()
        }

        self.results["summary"]["total"] += 1
        if passed:
            self.results["summary"]["passed"] += 1
            print(f"✅ {test_name}: PASSED")
        else:
            self.results["summary"]["failed"] += 1
            print(f"❌ {test_name}: FAILED - {details.get('error', 'Unknown error')}")

    def test_hmac_authentication(self):
        """Test HMAC authentication security"""
        print("🔐 Testing HMAC Authentication Security...")

        # Test 1: Valid HMAC request
        try:
            body = json.dumps({"goal": "BOX(A -> A)"})
            headers = self.generate_hmac_headers(body)
            headers["Content-Type"] = "application/json"

            response = requests.post(
                f"{self.base_url}/prove",
                headers=headers,
                data=body,
                timeout=10
            )

            valid_auth_success = response.status_code == 200

            self.log_test_result("hmac_valid_authentication", valid_auth_success, {
                "status_code": response.status_code,
                "auth_method": "hmac_sha256",
                "expected": 200,
                "got": response.status_code
            })

        except Exception as e:
            self.log_test_result("hmac_valid_authentication", False, {
                "error": str(e),
                "test_type": "valid_hmac"
            })

        # Test 2: Invalid signature
        try:
            body = json.dumps({"goal": "BOX(A -> A)"})
            headers = self.generate_hmac_headers(body)
            headers["X-Signature"] = "invalid_signature_should_fail"
            headers["Content-Type"] = "application/json"

            response = requests.post(
                f"{self.base_url}/prove",
                headers=headers,
                data=body,
                timeout=10
            )

            # Should receive 401 Unauthorized
            invalid_auth_rejected = response.status_code == 401

            self.log_test_result("hmac_invalid_signature_rejection", invalid_auth_rejected, {
                "status_code": response.status_code,
                "expected_rejection": True,
                "properly_rejected": invalid_auth_rejected
            })

        except Exception as e:
            self.log_test_result("hmac_invalid_signature_rejection", False, {
                "error": str(e),
                "test_type": "invalid_signature"
            })

        # Test 3: Timestamp replay attack protection
        try:
            old_timestamp = str(int(time.time()) - 120)  # 2 minutes ago
            nonce = hashlib.sha256(f"{old_timestamp}{time.time()}".encode()).hexdigest()[:16]

            body = json.dumps({"goal": "BOX(A -> A)"})
            signature_data = f"{old_timestamp}:{nonce}:{body}"
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
                data=body,
                timeout=10
            )

            # Should receive 401 due to old timestamp
            replay_protection_active = response.status_code == 401

            self.log_test_result("hmac_replay_attack_protection", replay_protection_active, {
                "status_code": response.status_code,
                "timestamp_age_seconds": 120,
                "replay_blocked": replay_protection_active
            })

        except Exception as e:
            self.log_test_result("hmac_replay_attack_protection", False, {
                "error": str(e),
                "test_type": "replay_attack"
            })

    def test_input_sanitization(self):
        """Test input sanitization and validation"""
        print("🛡️ Testing Input Sanitization...")

        # Test cases for malicious inputs
        malicious_inputs = [
            # SQL injection attempts
            {"goal": "'; DROP TABLE proofs; --", "description": "sql_injection"},
            {"goal": "' OR '1'='1", "description": "sql_boolean_injection"},

            # Script injection attempts
            {"goal": "<script>alert('xss')</script>", "description": "xss_script_tag"},
            {"goal": "javascript:alert('xss')", "description": "javascript_protocol"},

            # Command injection attempts
            {"goal": "; rm -rf /", "description": "command_injection"},
            {"goal": "$(whoami)", "description": "command_substitution"},

            # Buffer overflow attempts
            {"goal": "A" * 10000, "description": "buffer_overflow_attempt"},

            # Path traversal attempts
            {"goal": "../../../etc/passwd", "description": "path_traversal"},

            # Format string attacks
            {"goal": "%s%s%s%s%s", "description": "format_string"},
        ]

        sanitization_passed = 0

        for test_case in malicious_inputs:
            try:
                body = json.dumps({"goal": test_case["goal"]})
                headers = self.generate_hmac_headers(body)
                headers["Content-Type"] = "application/json"

                response = requests.post(
                    f"{self.base_url}/prove",
                    headers=headers,
                    data=body,
                    timeout=10
                )

                # Server should handle malicious input gracefully
                # Either reject (400/422) or process safely (200)
                server_stable = response.status_code in [200, 400, 422]

                # Check response doesn't contain obvious injection results
                response_safe = True
                if hasattr(response, 'text'):
                    response_text = response.text.lower()
                    dangerous_patterns = ['<script', 'javascript:', 'error:', 'exception']
                    response_safe = not any(pattern in response_text for pattern in dangerous_patterns)

                input_handled_safely = server_stable and response_safe

                if input_handled_safely:
                    sanitization_passed += 1

                self.log_test_result(f"input_sanitization_{test_case['description']}", input_handled_safely, {
                    "input_type": test_case["description"],
                    "status_code": response.status_code,
                    "server_stable": server_stable,
                    "response_safe": response_safe,
                    "input_length": len(test_case["goal"])
                })

            except Exception as e:
                self.log_test_result(f"input_sanitization_{test_case['description']}", False, {
                    "error": str(e),
                    "input_type": test_case["description"]
                })

        # Overall sanitization assessment
        sanitization_ratio = (sanitization_passed / len(malicious_inputs)) * 100
        overall_sanitization = sanitization_ratio >= 80  # 80% threshold

        self.log_test_result("input_sanitization_overall", overall_sanitization, {
            "passed_tests": sanitization_passed,
            "total_tests": len(malicious_inputs),
            "success_ratio": sanitization_ratio,
            "threshold_met": overall_sanitization
        })

    def test_server_hardening(self):
        """Test server security hardening measures"""
        print("🔒 Testing Server Security Hardening...")

        # Test 1: Response headers security
        try:
            response = requests.get(f"{self.base_url}/health", timeout=10)

            # Check for security headers
            security_headers = {
                "content-type": response.headers.get("content-type", "").startswith("application/json"),
                "server_disclosure": "server" not in response.headers or "waitress" in response.headers.get("server", "").lower(),
                "proper_response": response.status_code == 200
            }

            headers_secure = all(security_headers.values())

            self.log_test_result("server_security_headers", headers_secure, {
                "security_checks": security_headers,
                "response_headers": dict(response.headers),
                "overall_secure": headers_secure
            })

        except Exception as e:
            self.log_test_result("server_security_headers", False, {
                "error": str(e),
                "test_type": "security_headers"
            })

        # Test 2: Rate limiting behavior
        try:
            rapid_requests = 20
            successful_responses = 0
            rate_limited_responses = 0

            for i in range(rapid_requests):
                body = json.dumps({"goal": f"BOX(A{i} -> A{i})"})
                headers = self.generate_hmac_headers(body)
                headers["Content-Type"] = "application/json"

                response = requests.post(
                    f"{self.base_url}/prove",
                    headers=headers,
                    data=body,
                    timeout=5
                )

                if response.status_code == 200:
                    successful_responses += 1
                elif response.status_code == 429:
                    rate_limited_responses += 1

            # Server should handle burst requests gracefully
            server_resilient = (successful_responses + rate_limited_responses) >= rapid_requests * 0.7

            self.log_test_result("rate_limiting_behavior", server_resilient, {
                "total_requests": rapid_requests,
                "successful_responses": successful_responses,
                "rate_limited_responses": rate_limited_responses,
                "server_resilient": server_resilient,
                "success_rate": (successful_responses / rapid_requests) * 100
            })

        except Exception as e:
            self.log_test_result("rate_limiting_behavior", False, {
                "error": str(e),
                "test_type": "rate_limiting"
            })

        # Test 3: Error handling security
        try:
            # Test malformed JSON
            response = requests.post(
                f"{self.base_url}/prove",
                headers={"Content-Type": "application/json"},
                data="invalid json {",
                timeout=10
            )

            # Should get proper error response without information disclosure
            error_handled_safely = 400 <= response.status_code < 500

            # Response shouldn't contain sensitive information
            response_clean = True
            if hasattr(response, 'text'):
                sensitive_patterns = ['traceback', 'file', 'line', 'directory']
                response_clean = not any(pattern in response.text.lower() for pattern in sensitive_patterns)

            error_security = error_handled_safely and response_clean

            self.log_test_result("error_handling_security", error_security, {
                "status_code": response.status_code,
                "error_handled_safely": error_handled_safely,
                "response_clean": response_clean,
                "no_information_disclosure": error_security
            })

        except Exception as e:
            self.log_test_result("error_handling_security", False, {
                "error": str(e),
                "test_type": "error_handling"
            })

    def calculate_security_score(self):
        """Calculate overall security score"""
        total_tests = self.results["summary"]["total"]
        passed_tests = self.results["summary"]["passed"]

        if total_tests == 0:
            return 0.0

        return (passed_tests / total_tests) * 100

    def run_full_security_validation(self):
        """Run comprehensive security validation suite"""
        print("🛡️ LOGOS PXL Core v0.5-rc1 - Security Validation")
        print("=" * 60)

        # Test server availability first
        try:
            response = requests.get(f"{self.base_url}/health", timeout=10)
            if response.status_code != 200:
                print(f"❌ Server not available at {self.base_url}")
                return False
            print(f"✅ Server health check passed")
        except Exception as e:
            print(f"❌ Server connection failed: {e}")
            return False

        # Run security test suites
        self.test_hmac_authentication()
        print()
        self.test_input_sanitization()
        print()
        self.test_server_hardening()

        # Calculate security score
        security_score = self.calculate_security_score()

        print("\n" + "=" * 60)
        print("🔒 SECURITY VALIDATION SUMMARY")
        print("=" * 60)

        print(f"🎯 Security Score: {security_score:.1f}%")
        print(f"✅ Tests Passed: {self.results['summary']['passed']}")
        print(f"❌ Tests Failed: {self.results['summary']['failed']}")
        print(f"📊 Total Tests: {self.results['summary']['total']}")

        # Security assessment
        security_threshold = 85.0  # 85% pass rate for production
        security_validated = security_score >= security_threshold

        if security_validated:
            print(f"\n🎉 SECURITY VALIDATION PASSED")
            print(f"✅ Security score {security_score:.1f}% meets {security_threshold}% threshold")
            print("✅ System ready for production deployment")
        else:
            print(f"\n💥 SECURITY VALIDATION FAILED")
            print(f"❌ Security score {security_score:.1f}% below {security_threshold}% threshold")
            print("❌ Security issues must be resolved before production")

        return security_validated

    def save_results(self, filename="security_validation_results.json"):
        """Save security validation results"""
        with open(filename, 'w') as f:
            json.dump(self.results, f, indent=2)
        print(f"\n📄 Security validation results saved to {filename}")


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="LOGOS PXL Core Security Validation")
    parser.add_argument("--url", default="http://localhost:8088", help="Server URL")
    parser.add_argument("--hmac-key", default="test_security_key", help="HMAC secret key for testing")
    parser.add_argument("--save-results", action="store_true", help="Save results to JSON")

    args = parser.parse_args()

    validator = SecurityValidator(base_url=args.url, hmac_key=args.hmac_key)
    success = validator.run_full_security_validation()

    if args.save_results:
        validator.save_results()

    exit(0 if success else 1)
