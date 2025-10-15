import importlib
import pytest
from fastapi.testclient import TestClient

@pytest.mark.smoke
def test_metrics_endpoint():
    import services.tool_router.app as router_mod
    importlib.reload(router_mod)
    client = TestClient(router_mod.app)
    r = client.get("/metrics")
    assert r.status_code == 200
    assert b"router_requests_total" in r.content