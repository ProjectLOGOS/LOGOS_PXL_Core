import os

import requests
from fastapi import FastAPI, HTTPException
from pydantic import BaseModel

ROUTER = os.getenv("TOOL_ROUTER_URL", "http://127.0.0.1:8071")

app = FastAPI()


class ExecReq(BaseModel):
    action: str
    args: dict
    proof_token: dict


@app.get("/health")
def health():
    return {"ok": True}


@app.post("/execute")
def execute(x: ExecReq):
    if not x.proof_token or "kernel_hash" not in x.proof_token:
        raise HTTPException(403, "missing proof token")
    # Route actions to appropriate tools
    m = x.action.lower()
    if "cluster_texts" in m or "tetragnos" in m:
        tool = "tetragnos"
    elif "forecast_series" in m or "telos" in m:
        tool = "telos"
    elif "construct_proof" in m or "thonoc" in m:
        tool = "thonoc"
    elif "crawl" in m:
        tool = "crawl"
    elif m.startswith("http"):
        tool = "web"
    elif "write" in m:
        tool = "fs"
    else:
        tool = "db"
    r = requests.post(
        f"{ROUTER}/route",
        json={"tool": tool, "args": x.args, "proof_token": x.proof_token},
        timeout=15,
    )
    if not r.ok:
        raise HTTPException(r.status_code, r.text)
    return {"status": "OK", "result": r.json()}
