import importlib
import os
import pytest
from fastapi.testclient import TestClient

def _import_router_app(monkeypatch):
    monkeypatch.setenv("USE_REDIS_RATE_LIMIT", "true")
    monkeypatch.setenv("RATE_LIMIT_REQS", "2")
    monkeypatch.setenv("RATE_LIMIT_WINDOW_SECS", "60")
    # use fakeredis to avoid external service
    import sys
    import types
    class FakeRedis:
        def __init__(self): self.store={}
        def pipeline(self): return self
        def incr(self, k, v): self._k=k; self.store[k]=self.store.get(k,0)+v
        def expire(self, k, ttl): self._ttl=ttl
        def execute(self): return [self.store[self._k], True]
        def ping(self): return True
        @classmethod
        def from_url(cls, *a, **k): return cls()
    sys.modules["redis"]=types.SimpleNamespace(Redis=FakeRedis)
    import services.tool_router.app as router_mod
    importlib.reload(router_mod)
    return router_mod

@pytest.mark.smoke
def test_redis_rate_limit(monkeypatch):
    router_mod = _import_router_app(monkeypatch)
    app = router_mod.app
    client = TestClient(app)
    for _ in range(2):
        assert client.get("/health").status_code == 200
    assert client.get("/health").status_code == 429