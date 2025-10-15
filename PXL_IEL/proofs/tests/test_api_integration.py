"""
Integration test for LOGOS API with Tool Router.
Verifies end-to-end flow: authorize_action -> use proof token in tool router.
"""

import pytest
import requests
from fastapi.testclient import TestClient
import importlib


def test_api_router_integration(monkeypatch):
    """Test that LOGOS API proof tokens work with the tool router."""
    
    # Set high rate limits to avoid test interference
    monkeypatch.setenv("RATE_LIMIT_REQS", "10000")
    monkeypatch.setenv("RATE_LIMIT_WINDOW_SECS", "60")
    
    # Load LOGOS API
    monkeypatch.setenv("API_SIGNING_SECRET", "integration-test-secret")
    monkeypatch.setenv("TOKEN_TTL_SECS", "300")
    
    import services.logos_api.app as api_mod
    importlib.reload(api_mod)
    api_client = TestClient(api_mod.app)
    
    # Load Tool Router
    import services.tool_router.app as router_mod
    importlib.reload(router_mod)
    router_mod._buckets.clear()  # Clear rate limiter
    router_client = TestClient(router_mod.app)
    
    # Step 1: Get proof token from LOGOS API
    auth_response = api_client.post("/authorize_action", json={
        "action": "cluster_texts",
        "state": {"test": True}
    })
    
    assert auth_response.status_code == 200
    proof_token = auth_response.json()["proof_token"]
    
    # Verify proof token structure
    assert "token" in proof_token
    assert "exp" in proof_token
    assert "action_sha256" in proof_token
    assert "nonce" in proof_token
    
    # Step 2: Use proof token in tool router request
    # Mock the upstream tool response
    def mock_post(url, **kwargs):
        class MockResponse:
            status_code = 200
            def json(self):
                return {"ok": True, "clusters": [[0, 1]], "tool": "tetragnos"}
        return MockResponse()
    
    # Replace requests.post with our mock
    original_post = router_mod.requests.post
    router_mod.requests.post = mock_post
    
    try:
        # Make request to tool router with proof token
        router_response = router_client.post("/route", json={
            "tool": "tetragnos",
            "args": {"op": "cluster_texts", "texts": ["test1", "test2"]},
            "proof_token": proof_token
        })
        
        assert router_response.status_code == 200
        result = router_response.json()
        assert result["ok"] is True
        assert "data" in result
        assert "clusters" in result["data"]
        
    finally:
        # Restore original requests.post
        router_mod.requests.post = original_post


def test_api_kernel_verification_integration(monkeypatch):
    """Test kernel verification endpoint integration."""
    
    expected_hash = "test_kernel_hash_12345"
    monkeypatch.setenv("KERNEL_HASH", expected_hash)
    
    import services.logos_api.app as api_mod
    importlib.reload(api_mod)
    client = TestClient(api_mod.app)
    
    # Test matching hash
    response = client.post("/verify_kernel", json={"kernel_hash": expected_hash})
    assert response.status_code == 200
    result = response.json()
    assert result["ok"] is True
    assert result["match"] is True
    
    # Test non-matching hash
    response = client.post("/verify_kernel", json={"kernel_hash": "different_hash"})
    assert response.status_code == 200
    result = response.json()
    assert result["ok"] is True
    assert result["match"] is False


def test_api_token_expiration_validation(monkeypatch):
    """Test that proof tokens have reasonable expiration times."""
    
    import time
    monkeypatch.setenv("TOKEN_TTL_SECS", "120")  # 2 minutes
    
    import services.logos_api.app as api_mod
    importlib.reload(api_mod)
    client = TestClient(api_mod.app)
    
    start_time = int(time.time())
    
    response = client.post("/authorize_action", json={
        "action": "test_action",
        "state": {}
    })
    
    assert response.status_code == 200
    proof_token = response.json()["proof_token"]
    
    # Verify expiration is approximately 2 minutes from now
    expected_exp = start_time + 120
    actual_exp = proof_token["exp"]
    
    # Allow for some timing variance (±5 seconds)
    assert abs(actual_exp - expected_exp) <= 5
    
    # Ensure expiration is in the future
    assert actual_exp > start_time