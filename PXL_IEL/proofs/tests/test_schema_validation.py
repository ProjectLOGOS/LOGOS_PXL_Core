"""
Request schema validation tests. Why: ensure malformed requests are rejected.
"""
import importlib

import pytest
from fastapi.testclient import TestClient

pytestmark = pytest.mark.smoke


def _import_router_app():
    try:
        mod = importlib.import_module("services.tool_router.app")
        return mod.app
    except Exception:
        pytest.skip("services.tool_router.app:app not importable")


def test_unsupported_tool_rejected(monkeypatch):
    """Test that unsupported tools are rejected with validation error"""
    # Set very high rate limits to avoid test interference
    monkeypatch.setenv("RATE_LIMIT_REQS", "10000")
    monkeypatch.setenv("RATE_LIMIT_WINDOW_SECS", "60")
    
    # Clear rate limiter buckets to avoid interference
    import services.tool_router.app as router_mod  # type: ignore
    importlib.reload(router_mod)
    router_mod._buckets.clear()
    
    app = _import_router_app()
    client = TestClient(app)

    res = client.post(
        "/route",
        json={
            "tool": "invalid_tool",
            "args": {"some": "data"},
            "proof_token": {"token": "abc123"},
        },
    )
    assert res.status_code == 422
    # FastAPI validation errors return 'detail' field with validation info
    response_data = res.json()
    assert "detail" in response_data
    # Verify the detail contains validation error information
    assert isinstance(response_data["detail"], list)


def test_missing_proof_token_fields(monkeypatch):
    """Test that missing proof token fields are rejected"""
    # Set very high rate limits to avoid test interference
    monkeypatch.setenv("RATE_LIMIT_REQS", "10000")
    monkeypatch.setenv("RATE_LIMIT_WINDOW_SECS", "60")
    
    # Clear rate limiter buckets to avoid interference
    import services.tool_router.app as router_mod  # type: ignore
    importlib.reload(router_mod)
    router_mod._buckets.clear()
    
    app = _import_router_app()
    client = TestClient(app)

    res = client.post(
        "/route",
        json={
            "tool": "tetragnos",
            "args": {"op": "test"},
            "proof_token": {},  # Missing token
        },
    )
    assert res.status_code == 422
    # FastAPI validation errors return 'detail' field with validation info
    response_data = res.json()
    assert "detail" in response_data
    # Verify the detail contains validation error information
    assert isinstance(response_data["detail"], list)


def test_valid_tools_accepted(monkeypatch):
    """Test that all valid tools are accepted by validation"""
    # Clear rate limiter buckets
    import services.tool_router.app as router_mod  # type: ignore
    router_mod._buckets.clear()
    
    app = _import_router_app()
    client = TestClient(app)

    valid_tools = ["tetragnos", "thonoc", "telos", "web", "db", "fs", "crawl"]

    for tool in valid_tools:
        res = client.post(
            "/route",
            json={
                "tool": tool,
                "args": {"test": "data"},
                "proof_token": {"token": "abc123"},
            },
        )
        # Should not fail validation (might fail on network, but that's 502 not 422)
        assert res.status_code != 422, f"Tool {tool} failed validation"