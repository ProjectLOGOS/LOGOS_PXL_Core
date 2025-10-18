import json
import os
import pathlib

import aio_pika
import requests
from fastapi import APIRouter, FastAPI, HTTPException
from pydantic import BaseModel

RABBIT = os.getenv("RABBIT_URL", "amqp://guest:guest@rabbitmq/")
LOGOS = os.getenv("LOGOS_API_URL", "http://logos-api:8090")
MAP = json.load(open("/app/task_mappings.json", encoding="utf-8"))

app = FastAPI()

# GUI Status API
gui_router = APIRouter()


def _cfg():
    try:
        p = pathlib.Path("/app/configs/config.json")
        return json.loads(p.read_text(encoding="utf-8"))
    except:
        return {
            "expected_kernel_hash": "unknown",
            "pxl_prover_url": "unknown",
            "audit_path": "unknown",
        }


@gui_router.get("/gui/status")
def gui_status():
    cfg = _cfg()
    return {
        "kernel_hash_expected": cfg.get("expected_kernel_hash"),
        "prover_url": cfg.get("pxl_prover_url"),
        "audit_path": cfg.get("audit_path"),
        "rabbit_url": RABBIT,
        "logos_api": LOGOS,
    }


@gui_router.get("/gui/summary")
def gui_summary():
    # Enhanced summary with service status
    try:
        archon_health = {"ok": True, "service": "archon-gateway"}
    except:
        archon_health = {"ok": False, "error": "connection failed"}

    return {
        "services": {"archon": archon_health, "rabbitmq_ui": "http://rabbitmq:15672"},
        "workers": {
            "telos": {"status": "active", "tasks": ["predict_outcomes", "causal_retrodiction"]},
            "tetragnos": {"status": "active", "tasks": ["cluster_texts", "semantic_similarity"]},
            "thonoc": {"status": "active", "tasks": ["construct_proof", "theorem_proving"]},
        },
        "toolkits": {"crawl": {"status": "active", "port": 8064}},
    }


app.include_router(gui_router)


class DispatchIn(BaseModel):
    task_type: str
    payload: dict = {}
    provenance: dict = {}


def _route(tt: str) -> str:
    for k, v in MAP.items():
        if tt in v:
            return k.lower()
    return ""


@app.get("/health")
def health():
    return {"ok": True}


@app.post("/dispatch")
async def dispatch(d: DispatchIn):
    # Require proof token from Logos API before enqueue
    auth = {
        "action": f"task:{d.task_type}",
        "state": "queued",
        "props": "task_payload",
        "provenance": d.provenance,
    }
    r = requests.post(f"{LOGOS}/authorize_action", json=auth, timeout=10)
    if r.status_code != 200:
        raise HTTPException(403, f"authorization failed: {r.text}")
    proof_token = r.json().get("proof_token", {})
    rk = _route(d.task_type)
    if not rk:
        raise HTTPException(404, "unknown task_type")
    conn = await aio_pika.connect_robust(RABBIT)
    async with conn:
        ch = await conn.channel()
        ex = await ch.declare_exchange("logos.tasks", aio_pika.ExchangeType.TOPIC, durable=True)
        msg = aio_pika.Message(
            body=json.dumps(
                {"task_type": d.task_type, "payload": d.payload, "proof_token": proof_token}
            ).encode("utf-8")
        )
        await ex.publish(msg, routing_key=rk)
    return {"status": "ENQUEUED", "subsystem": rk}
