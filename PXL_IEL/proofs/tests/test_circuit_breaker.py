import importlib
import pytest
from fastapi.testclient import TestClient

@pytest.mark.smoke
def test_circuit_open_then_half_open(monkeypatch):
    monkeypatch.setenv("CB_FAIL_THRESHOLD", "2")
    monkeypatch.setenv("CB_COOLDOWN_SECS", "1")
    import services.tool_router.app as router_mod
    importlib.reload(router_mod)
    app = router_mod.app
    client = TestClient(app)

    # make upstream fail
    def fail_post(url, json, headers, timeout):
        raise router_mod.requests.RequestException("boom")
    router_mod.requests.post = fail_post  # type: ignore

    body = {"tool":"tetragnos","args":{},"proof_token":{"token":"x"}}
    # trigger failures to open circuit
    for _ in range(2):
        r = client.post("/route", json=body)
        assert r.status_code in (502, 503)  # 502 for upstream error, 503 for circuit open

    # circuit open -> immediate 503
    r = client.post("/route", json=body)
    assert r.status_code == 503

    # cooldown
    import time; time.sleep(1.1)

    # half-open attempt still fails -> back to open quickly
    r = client.post("/route", json=body)
    assert r.status_code in (502, 503)