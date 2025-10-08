import importlib
import json
import time
import hmac
import hashlib
import os
import pytest
from fastapi.testclient import TestClient

def _import_router_app():
    try:
        mod = importlib.import_module("services.tool_router.app")
        return mod
    except Exception:
        pytest.skip("router not importable")

def _sign(secret: str, body: dict):
    ts = str(int(time.time()))
    # Use the same JSON formatting that will be sent by the client
    json_body = json.dumps(body, separators=(',', ':'))
    msg = f"{ts}.{json_body}".encode()
    sig = hmac.new(secret.encode(), msg, hashlib.sha256).hexdigest()
    return ts, sig

@pytest.mark.smoke
def test_hmac_success(monkeypatch):
    monkeypatch.setenv("SIGNING_SECRET", "secret")
    import services.tool_router.app as router_mod
    importlib.reload(router_mod)
    app = router_mod.app
    client = TestClient(app)

    body = {"tool":"tetragnos","args":{"op":"x"},"proof_token":{"token":"t"}}
    ts, sig = _sign("secret", body)
    # mock upstream
    def fake_post(url, json, headers, timeout):
        class R: 
            status_code=200
            text=""
            def json(self): return {"ok": True}
        return R()
    router_mod.requests.post = fake_post  # type: ignore
    r = client.post("/route", json=body, headers={"X-Timestamp": ts, "X-Signature": sig})
    assert r.status_code == 200
    assert r.json()["ok"] is True

@pytest.mark.smoke
def test_hmac_failure(monkeypatch):
    monkeypatch.setenv("SIGNING_SECRET", "secret")
    import services.tool_router.app as router_mod
    importlib.reload(router_mod)
    app = router_mod.app
    client = TestClient(app)

    body = {"tool":"tetragnos","args":{"op":"x"},"proof_token":{"token":"t"}}
    r = client.post("/route", json=body, headers={"X-Timestamp": "0", "X-Signature": "bad"})
    assert r.status_code == 401