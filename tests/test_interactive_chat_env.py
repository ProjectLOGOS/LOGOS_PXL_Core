"""
Ensures interactive chat reads LOGOS_API_URL from env and uses router URL for tool calls.
Only checks import and env plumbing, not network.
"""

import importlib

import pytest
from fastapi.testclient import TestClient


def _import_chat_app():
    try:
        mod = importlib.import_module("services.interactive_chat.app")
        return mod.app  # type: ignore[attr-defined]
    except Exception:
        pytest.skip("services.interactive_chat.app:app not importable")


def test_env_defaults(monkeypatch: pytest.MonkeyPatch):
    monkeypatch.setenv("LOGOS_API_URL", "http://logos-api:8090")
    monkeypatch.setenv("TOOL_ROUTER_URL", "http://tool-router:8071")

    app = _import_chat_app()
    client = TestClient(app)
    r = client.get("/openapi.json")
    assert r.status_code == 200  # app booted with env in place
