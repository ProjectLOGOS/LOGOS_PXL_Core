from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
import os, json, asyncio, aio_pika, requests

RABBIT = os.getenv("RABBIT_URL","amqp://guest:guest@rabbitmq/")
LOGOS  = os.getenv("LOGOS_API_URL","http://logos-api:8090")
MAP    = json.load(open("/app/task_mappings.json","r",encoding="utf-8"))

app = FastAPI()

class DispatchIn(BaseModel):
    task_type: str
    payload: dict = {}
    provenance: dict = {}

def _route(tt: str)->str:
    for k,v in MAP.items():
        if tt in v: return k.lower()
    return ""

@app.get("/health")
def health(): return {"ok": True}

@app.post("/dispatch")
async def dispatch(d: DispatchIn):
    # Require proof token from Logos API before enqueue
    auth = {"action": f"task:{d.task_type}", "state": "queued", "props": "task_payload", "provenance": d.provenance}
    r = requests.post(f"{LOGOS}/authorize_action", json=auth, timeout=10)
    if r.status_code != 200:
        raise HTTPException(403, f"authorization failed: {r.text}")
    proof_token = r.json().get("proof_token", {})
    rk = _route(d.task_type)
    if not rk: raise HTTPException(404, "unknown task_type")
    conn = await aio_pika.connect_robust(RABBIT)
    async with conn:
        ch = await conn.channel()
        ex = await ch.declare_exchange("logos.tasks", aio_pika.ExchangeType.TOPIC, durable=True)
        msg = aio_pika.Message(body=json.dumps({
            "task_type": d.task_type, "payload": d.payload, "proof_token": proof_token
        }).encode("utf-8"))
        await ex.publish(msg, routing_key=rk)
    return {"status":"ENQUEUED","subsystem":rk}
