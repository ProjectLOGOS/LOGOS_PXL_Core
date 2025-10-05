from fastapi import FastAPI
import os, json, asyncio, aio_pika

RABBIT = os.getenv("RABBIT_URL","amqp://guest:guest@rabbitmq/")
SUBSYS = os.getenv("SUBSYS","worker")
ROUTE  = os.getenv("ROUTE","")

app = FastAPI()
@app.get("/health")
def health(): return {"ok": True, "subsystem": SUBSYS}

async def handle(msg: aio_pika.IncomingMessage):
    async with msg.process():
        data = json.loads(msg.body.decode("utf-8"))
        token = data.get("proof_token",{})
        if not token or "kernel_hash" not in token:
            return  # drop silently; alignment core not satisfied
        # TODO: call actual toolkit logic here based on SUBSYS and data["task_type"]
        print(f"[{SUBSYS}] processed {data['task_type']}")

async def main():
    conn = await aio_pika.connect_robust(RABBIT)
    ch = await conn.channel()
    await ch.set_qos(prefetch_count=10)
    ex = await ch.declare_exchange("logos.tasks", aio_pika.ExchangeType.TOPIC, durable=True)
    q = await ch.declare_queue(f"q.{ROUTE}", durable=True)
    await q.bind(ex, ROUTE)
    await q.consume(handle)
    print(f"[{SUBSYS}] listening on route '{ROUTE}'")
    return conn

@app.on_event("startup")
async def _startup():
    app.state.conn = await main()
