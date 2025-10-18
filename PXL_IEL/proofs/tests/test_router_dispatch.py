"""
Validates Tool Router request model, proof token pass-through, and dispatch.
Downstream HTTP calls are mocked to avoid requiring live services.
"""

import importlib
from typing import Any

import pytest
from fastapi.testclient import TestClient

pytestmark = pytest.mark.smoke


def _import_router_app():
    try:
        mod = importlib.import_module("services.tool_router.app")
        return mod.app  # type: ignore[attr-defined]
    except Exception:
        pytest.skip("services.tool_router.app:app not importable")


class _Resp:
    # Minimal adapter to mimic requests.Response
    def __init__(self, status_code: int, payload: dict[str, Any]) -> None:
        self.status_code = status_code
        self._payload = payload

    def json(self) -> dict[str, Any]:
        return self._payload

    @property
    def ok(self) -> bool:
        return 200 <= self.status_code < 300

    @property
    def text(self) -> str:
        return str(self._payload)


def test_route_tetragnos_and_thonoc(monkeypatch: pytest.MonkeyPatch):
    # Set very high rate limits to avoid test interference
    monkeypatch.setenv("RATE_LIMIT_REQS", "10000")
    monkeypatch.setenv("RATE_LIMIT_WINDOW_SECS", "60")

    # Clear rate limiter buckets to avoid interference
    import services.tool_router.app as router_mod  # type: ignore
    importlib.reload(router_mod)
    router_mod._buckets.clear()

    app = _import_router_app()
    client = TestClient(app)

    calls: list[dict] = []

    def fake_post(url: str, json: dict[str, Any] | None = None, timeout: int | float | None = None, headers: dict[str, str] | None = None):
        calls.append({"url": url, "json": json, "headers": headers})
        if "tetragnos" in url:
            return _Resp(200, {"ok": True, "clusters": [[0, 1]], "tool": "tetragnos"})
        if "thonoc" in url:
            return _Resp(200, {"ok": True, "proved": True, "tool": "thonoc"})
        return _Resp(404, {"ok": False})

    import services.tool_router.app as router_mod  # type: ignore

    monkeypatch.setenv("TETRAGNOS_URL", "http://tetragnos:8000")
    monkeypatch.setenv("THONOC_URL", "http://thonoc:8000")

    # Mock requests module with exceptions
    class MockRequestException(Exception):
        pass

    mock_requests = type(
        "MockRequests",
        (),
        {
            "post": fake_post,
            "RequestException": MockRequestException,
        },
    )
    monkeypatch.setattr(router_mod, "requests", mock_requests)

    res1 = client.post(
        "/route",
        json={
            "tool": "tetragnos",
            "args": {"op": "cluster_texts", "texts": ["a", "b"]},
            "proof_token": {"token": "abc123"},
        },
    )
    assert res1.status_code == 200
    assert res1.json()["ok"] is True
    assert res1.json()["tool"] == "tetragnos"
    assert res1.json()["data"]["tool"] == "tetragnos"

    res2 = client.post(
        "/route",
        json={
            "tool": "thonoc",
            "args": {"formula": "A->B"},
            "proof_token": {"token": "abc123"},
        },
    )
    assert res2.status_code == 200
    assert res2.json()["ok"] is True
    assert res2.json()["tool"] == "thonoc"
    assert res2.json()["data"]["tool"] == "thonoc"

    assert any("tetragnos" in c["url"] for c in calls)
    assert any("thonoc" in c["url"] for c in calls)
