"""
Basic rate limit behavior. Why: prevent regression in middleware.
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


def test_rate_limit_trip(monkeypatch):
    """Test that rate limiting kicks in after exceeding the limit"""
    app = _import_router_app()
    monkeypatch.setenv("RATE_LIMIT_REQS", "3")
    monkeypatch.setenv("RATE_LIMIT_WINDOW_SECS", "60")

    # re-import to apply env
    import services.tool_router.app as router_mod  # type: ignore

    importlib.reload(router_mod)
    client = TestClient(router_mod.app)

    # hit health quickly to avoid upstream noise
    for _ in range(3):
        r = client.get("/health")
        assert r.status_code == 200
    r = client.get("/health")
    assert r.status_code == 429
    assert "Retry-After" in r.headers


def test_rate_limit_api_key_vs_ip(monkeypatch):
    """Test that API key and IP have separate buckets"""
    monkeypatch.setenv("RATE_LIMIT_REQS", "2")
    monkeypatch.setenv("RATE_LIMIT_WINDOW_SECS", "60")

    import services.tool_router.app as router_mod  # type: ignore

    importlib.reload(router_mod)
    client = TestClient(router_mod.app)

    # Exhaust IP bucket
    for _ in range(2):
        r = client.get("/health")
        assert r.status_code == 200

    # IP should be rate limited
    r = client.get("/health")
    assert r.status_code == 429

    # But API key should still work
    r = client.get("/health", headers={"X-API-Key": "test-key"})
    assert r.status_code == 200
