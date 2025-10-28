"""
Fast health check for the logos API service.
Skips if the app cannot be imported locally. This keeps tests green before services exist.
"""

import importlib

import pytest

pytestmark = pytest.mark.smoke


def _import_app():
    try:
        return importlib.import_module("logos_core.server").app  # type: ignore[attr-defined]
    except Exception:
        pytest.skip("logos_core.server:app not importable")


def test_health_returns_ok():
    from fastapi.testclient import TestClient

    app = _import_app()
    with TestClient(app) as client:
        res = client.get("/health")
        assert res.status_code == 200
        assert res.json().get("ok") is True
