import hashlib
import time
import urllib.robotparser as rp
from urllib.parse import urlparse

import requests
from fastapi import FastAPI, HTTPException
from pydantic import BaseModel

ALLOWED = {"example.org", "arxiv.org", "acm.org"}  # edit allowlist

app = FastAPI()


@app.get("/health")
def health():
    return {"ok": True}


class T(BaseModel):
    tool: str
    args: dict
    proof_token: dict


def _ok(url: str) -> bool:
    try:
        u = urlparse(url)
        if u.scheme not in ("http", "https"):
            return False
        if u.hostname not in ALLOWED:
            return False
        rob = rp.RobotFileParser()
        rob.set_url(f"{u.scheme}://{u.hostname}/robots.txt")
        try:
            rob.read()
            if not rob.can_fetch("*", url):
                return False
        except Exception:
            return False
        return True
    except Exception:
        return False


@app.post("/invoke")
def invoke(t: T):
    if not t.proof_token or "kernel_hash" not in t.proof_token:
        raise HTTPException(403, "missing proof token")
    url = t.args.get("url")
    if not url or not _ok(url):
        raise HTTPException(403, "url not allowed")
    r = requests.get(url, timeout=10)
    body = r.text[:2000]
    h = hashlib.sha256(r.content).hexdigest()
    return {
        "ok": True,
        "url": url,
        "status": r.status_code,
        "sha256": h,
        "snippet": body,
        "fetched_at": int(time.time() * 1000),
    }
