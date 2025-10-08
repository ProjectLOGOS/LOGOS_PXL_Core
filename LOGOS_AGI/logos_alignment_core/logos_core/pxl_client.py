import json
import urllib.error
import urllib.request


class PXLClient:
    def __init__(self, base_url: str, timeout_ms: int = 2000):
        self.base_url = base_url.rstrip("/")
        self.timeout = timeout_ms / 1000.0

    def _post(self, path: str, payload: dict) -> dict:
        data = json.dumps(payload).encode("utf-8")
        req = urllib.request.Request(
            self.base_url + path, data=data, headers={"Content-Type": "application/json"}
        )
        with urllib.request.urlopen(req, timeout=self.timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))

    def prove_box(self, phi: str):
        try:
            out = self._post("/prove", {"goal": f"BOX({phi})"})
            return bool(out.get("ok", False)), out
        except (TimeoutError, urllib.error.URLError):
            return False, {"error": "prover_unreachable"}
