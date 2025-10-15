"""
Unit tests for LOGOS API:
- /health 200
- /authorize_action returns valid token fields
- HMAC signing path generates deterministic token digest
- /verify_kernel compares against configured KERNEL_HASH
"""

import importlib
import os
import re
import time
import hmac
import hashlib
import pytest
from fastapi.testclient import TestClient

def _load_app(monkeypatch: pytest.MonkeyPatch, **env):
    for k, v in env.items():
        monkeypatch.setenv(k, v)
    import services.logos_api.app as api_mod
    importlib.reload(api_mod)
    return api_mod, TestClient(api_mod.app)

def test_health_ok(monkeypatch):
    mod, client = _load_app(monkeypatch)
    r = client.get("/health")
    assert r.status_code == 200
    assert r.json() == {"ok": True}

def test_authorize_action_unsigned(monkeypatch):
    mod, client = _load_app(monkeypatch, TOKEN_TTL_SECS="60", API_SIGNING_SECRET="")
    r = client.post("/authorize_action", json={"action": "cluster_texts", "state": {}})
    assert r.status_code == 200
    js = r.json()
    assert js["ok"] is True
    pt = js["proof_token"]
    assert isinstance(pt["token"], str) and len(pt["token"]) > 10
    assert pt["action_sha256"] == hashlib.sha256(b"cluster_texts").hexdigest()
    assert pt["exp"] > int(time.time())

def test_authorize_action_hmac_signed(monkeypatch):
    mod, client = _load_app(monkeypatch, TOKEN_TTL_SECS="60", API_SIGNING_SECRET="secret")
    r = client.post("/authorize_action", json={"action": "prove", "state": {}})
    assert r.status_code == 200
    pt = r.json()["proof_token"]
    payload = f"{pt['nonce']}.{pt['exp']}.{pt['action_sha256']}"
    expect = hmac.new(b"secret", payload.encode(), hashlib.sha256).hexdigest()
    assert pt["token"] == expect

def test_verify_kernel_match(monkeypatch):
    expect = "deadbeef"
    mod, client = _load_app(monkeypatch, KERNEL_HASH=expect)
    r = client.post("/verify_kernel", json={"kernel_hash": expect})
    assert r.status_code == 200
    assert r.json() == {"ok": True, "match": True}

def test_verify_kernel_mismatch(monkeypatch):
    mod, client = _load_app(monkeypatch, KERNEL_HASH="aabbcc")
    r = client.post("/verify_kernel", json={"kernel_hash": "zz11"})
    assert r.status_code == 200
    assert r.json() == {"ok": True, "match": False}

def test_verify_kernel_missing_value(monkeypatch):
    mod, client = _load_app(monkeypatch)
    r = client.post("/verify_kernel", json={"kernel_hash": ""})
    assert r.status_code == 400