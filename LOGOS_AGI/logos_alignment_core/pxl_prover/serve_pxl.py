#!/usr/bin/env python3
import json
import random
import string
from http.server import BaseHTTPRequestHandler, HTTPServer

KERNEL_HASH = "DEADBEEF-STUB"


def _ok(goal: str) -> bool:
    return "DENY" not in goal.upper()


class Handler(BaseHTTPRequestHandler):
    def _send(self, code, payload):
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.end_headers()
        self.wfile.write(json.dumps(payload).encode("utf-8"))

    def do_POST(self):
        length = int(self.headers.get("Content-Length", "0"))
        body = self.rfile.read(length).decode("utf-8")
        try:
            data = json.loads(body) if body else {}
        except json.JSONDecodeError:
            return self._send(400, {"ok": False, "error": "bad_json"})
        goal = data.get("goal", "")
        if self.path == "/prove":
            ok = _ok(goal)
            payload = {
                "ok": ok,
                "id": "pf_" + "".join(random.choices(string.ascii_lowercase + string.digits, k=8)),
                "kernel_hash": KERNEL_HASH,
                "goal": goal,
            }
            return self._send(200, payload)
        elif self.path == "/countermodel":
            return self._send(200, {"found": False, "goal": goal})
        return self._send(404, {"ok": False, "error": "unknown_endpoint"})


if __name__ == "__main__":
    HTTPServer(("0.0.0.0", 8088), Handler).serve_forever()
