#!/usr/bin/env python3
"""
LOGOS AGI Security Module
HMAC-SHA256 Request Authentication with Anti-Replay Protection
Week 3: Security Hardening Implementation
"""

import hmac
import hashlib
import time
import secrets
import json
import logging
from typing import Dict, Optional, Tuple, Set
from dataclasses import dataclass
from threading import Lock
from collections import OrderedDict
from flask import Request, jsonify
import base64


# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class SecurityConfig:
    """Security configuration parameters"""
    hmac_secret_key: bytes
    max_timestamp_drift_seconds: int = 60
    nonce_cache_size: int = 10000
    nonce_cache_ttl_seconds: int = 300
    request_timeout_seconds: int = 30


class NonceTracker:
    """Thread-safe nonce tracking for replay attack prevention"""

    def __init__(self, max_size: int = 10000, ttl_seconds: int = 300):
        self.max_size = max_size
        self.ttl_seconds = ttl_seconds
        self.nonces: OrderedDict[str, float] = OrderedDict()
        self.lock = Lock()

    def is_nonce_used(self, nonce: str) -> bool:
        """Check if nonce has been used (replay attack detection)"""
        current_time = time.time()

        with self.lock:
            # Clean expired nonces
            self._cleanup_expired(current_time)

            # Check if nonce already exists
            if nonce in self.nonces:
                logger.warning(f"Replay attack detected: nonce {nonce} already used")
                return True

            # Add nonce to tracking
            self.nonces[nonce] = current_time

            # Maintain size limit (LRU eviction)
            while len(self.nonces) > self.max_size:
                self.nonces.popitem(last=False)

            return False

    def _cleanup_expired(self, current_time: float):
        """Remove expired nonces from cache"""
        expired_keys = [
            nonce for nonce, timestamp in self.nonces.items()
            if current_time - timestamp > self.ttl_seconds
        ]
        for key in expired_keys:
            del self.nonces[key]

    def get_stats(self) -> Dict[str, any]:
        """Get nonce tracking statistics"""
        with self.lock:
            return {
                "total_nonces": len(self.nonces),
                "max_size": self.max_size,
                "ttl_seconds": self.ttl_seconds
            }


class HMACAuthenticator:
    """HMAC-SHA256 request authentication with anti-replay protection"""

    def __init__(self, config: SecurityConfig):
        self.config = config
        self.nonce_tracker = NonceTracker(
            max_size=config.nonce_cache_size,
            ttl_seconds=config.nonce_cache_ttl_seconds
        )
        logger.info("HMAC Authenticator initialized with anti-replay protection")

    def generate_signature(self, method: str, path: str, body: str,
                         timestamp: str, nonce: str) -> str:
        """Generate HMAC-SHA256 signature for request"""
        # Create canonical request string
        canonical_request = f"{method}\n{path}\n{body}\n{timestamp}\n{nonce}"

        # Generate HMAC signature
        signature = hmac.new(
            self.config.hmac_secret_key,
            canonical_request.encode('utf-8'),
            hashlib.sha256
        ).hexdigest()

        return signature

    def validate_timestamp(self, timestamp_str: str) -> bool:
        """Validate request timestamp to prevent stale requests"""
        try:
            request_timestamp = float(timestamp_str)
            current_timestamp = time.time()

            # Check for timestamp drift
            drift = abs(current_timestamp - request_timestamp)

            if drift > self.config.max_timestamp_drift_seconds:
                logger.warning(f"Request timestamp drift too large: {drift}s > {self.config.max_timestamp_drift_seconds}s")
                return False

            return True

        except (ValueError, TypeError) as e:
            logger.warning(f"Invalid timestamp format: {e}")
            return False

    def authenticate_request(self, request: Request) -> Tuple[bool, Optional[str]]:
        """
        Authenticate incoming request using HMAC-SHA256
        Returns: (is_authenticated, error_message)
        """
        try:
            # Extract authentication headers
            auth_header = request.headers.get('Authorization')
            timestamp = request.headers.get('X-Timestamp')
            nonce = request.headers.get('X-Nonce')

            if not auth_header or not timestamp or not nonce:
                return False, "Missing required authentication headers"

            # Parse authorization header
            if not auth_header.startswith('HMAC-SHA256 '):
                return False, "Invalid authorization header format"

            provided_signature = auth_header[12:]  # Remove 'HMAC-SHA256 ' prefix

            # Validate timestamp
            if not self.validate_timestamp(timestamp):
                return False, "Request timestamp invalid or too old"

            # Check for nonce replay
            if self.nonce_tracker.is_nonce_used(nonce):
                return False, "Nonce replay detected - potential attack"

            # Get request body
            if request.is_json:
                body = json.dumps(request.get_json(), sort_keys=True, separators=(',', ':'))
            else:
                body = request.get_data(as_text=True)

            # Generate expected signature
            expected_signature = self.generate_signature(
                method=request.method,
                path=request.path,
                body=body,
                timestamp=timestamp,
                nonce=nonce
            )

            # Perform constant-time comparison
            if not hmac.compare_digest(provided_signature, expected_signature):
                logger.warning(f"HMAC signature mismatch for {request.method} {request.path}")
                return False, "Authentication signature invalid"

            # Log successful authentication
            logger.info(f"Request authenticated: {request.method} {request.path}")
            return True, None

        except Exception as e:
            logger.error(f"Authentication error: {e}")
            return False, f"Authentication error: {str(e)}"

    def create_client_signature(self, method: str, path: str, body: str = "") -> Dict[str, str]:
        """
        Helper method to create client-side authentication headers
        Used for testing and client implementations
        """
        timestamp = str(int(time.time()))
        nonce = secrets.token_hex(16)

        signature = self.generate_signature(method, path, body, timestamp, nonce)

        return {
            'Authorization': f'HMAC-SHA256 {signature}',
            'X-Timestamp': timestamp,
            'X-Nonce': nonce
        }

    def get_security_stats(self) -> Dict[str, any]:
        """Get security authentication statistics"""
        return {
            "nonce_stats": self.nonce_tracker.get_stats(),
            "config": {
                "max_timestamp_drift": self.config.max_timestamp_drift_seconds,
                "nonce_cache_size": self.config.nonce_cache_size,
                "nonce_ttl": self.config.nonce_cache_ttl_seconds
            }
        }


def create_security_middleware(config: SecurityConfig):
    """Create Flask middleware for HMAC authentication"""
    authenticator = HMACAuthenticator(config)

    def security_middleware():
        """Flask before_request middleware for authentication"""
        from flask import request, jsonify

        # Skip authentication for health endpoints
        if request.path.startswith('/health'):
            return None

        # Authenticate request
        is_authenticated, error_message = authenticator.authenticate_request(request)

        if not is_authenticated:
            logger.warning(f"Authentication failed: {error_message} for {request.remote_addr}")
            return jsonify({
                "error": "Authentication failed",
                "message": error_message,
                "timestamp": int(time.time())
            }), 401

        return None

    return security_middleware, authenticator


def generate_hmac_secret() -> bytes:
    """Generate a cryptographically secure HMAC secret key"""
    return secrets.token_bytes(32)  # 256-bit key


# Example usage and testing
if __name__ == "__main__":
    # Generate a secret key (in production, store securely)
    secret_key = generate_hmac_secret()

    # Create security configuration
    config = SecurityConfig(
        hmac_secret_key=secret_key,
        max_timestamp_drift_seconds=60,
        nonce_cache_size=10000
    )

    # Create authenticator
    authenticator = HMACAuthenticator(config)

    # Example: Create client signature
    headers = authenticator.create_client_signature(
        method="POST",
        path="/prove",
        body='{"goal": "BOX(Good(test))"}'
    )

    print("Example HMAC Authentication Headers:")
    for key, value in headers.items():
        print(f"{key}: {value}")

    # Example: Performance test
    import time
    start_time = time.time()

    for i in range(1000):
        test_headers = authenticator.create_client_signature("GET", f"/test/{i}")

    end_time = time.time()
    print(f"\nPerformance: 1000 signature generations in {(end_time - start_time)*1000:.2f}ms")
    print(f"Average: {(end_time - start_time):.4f}ms per signature")
