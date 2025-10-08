import importlib
import json
import os

import aio_pika

RABBIT = os.getenv("RABBIT_URL", "amqp://guest:guest@rabbitmq/")
SUBSYS = os.getenv("SUBSYS", "WORKER")
ROUTE = os.getenv("ROUTE", "route")
V4PATH = os.getenv("V4PATH", "/v4")  # mounted host v4 path

# Map task_type -> (module,function)
TASKMAP = {
    # TELOS
    "predict_outcomes": ("v4.telos_worker", "predict_outcomes"),
    "causal_retrodiction": ("v4.telos_worker", "causal_retrodiction"),
    "analyze_intervention": ("v4.telos_worker", "analyze_intervention"),
    "forecast_series": ("v4.telos_worker", "forecast_series"),
    "test_hypothesis": ("v4.telos_worker", "test_hypothesis"),
    "build_causal_model": ("v4.telos_worker", "build_causal_model"),
    # TETRAGNOS
    "cluster_texts": ("v4.tetragnos_worker", "cluster_texts"),
    "translate_text": ("v4.tetragnos_worker", "translate_text"),
    "extract_features": ("v4.tetragnos_worker", "extract_features"),
    "analyze_patterns": ("v4.tetragnos_worker", "analyze_patterns"),
    "semantic_similarity": ("v4.tetragnos_worker", "semantic_similarity"),
    # THONOC
    "construct_proof": ("v4.thonoc_worker", "construct_proof"),
    "assign_consequence": ("v4.thonoc_worker", "assign_consequence"),
    "evaluate_lambda": ("v4.thonoc_worker", "evaluate_lambda"),
    "modal_reasoning": ("v4.thonoc_worker", "modal_reasoning"),
    "consistency_check": ("v4.thonoc_worker", "consistency_check"),
    "theorem_proving": ("v4.thonoc_worker", "theorem_proving"),
}


def _resolve(task_type: str):
    if task_type not in TASKMAP:
        raise KeyError(f"unknown task_type: {task_type}")
    mod, fn = TASKMAP[task_type]
    m = importlib.import_module(mod)
    return getattr(m, fn)


async def handle(msg: aio_pika.IncomingMessage):
    async with msg.process():
        data = json.loads(msg.body.decode("utf-8"))
        token = data.get("proof_token", {})
        if not token or "kernel_hash" not in token:
            return  # drop; alignment core not satisfied
        fn = _resolve(data["task_type"])
        res = (
            fn(**data.get("payload", {}))
            if callable(fn)
            else {"ok": False, "err": "fn not callable"}
        )
        print(f"[{SUBSYS}] {data['task_type']} -> OK")
        # TODO: publish results to a results topic or persist as needed


async def main():
    import sys

    sys.path.insert(0, V4PATH)
    conn = await aio_pika.connect_robust(RABBIT)
    ch = await conn.channel()
    await ch.set_qos(prefetch_count=16)
    ex = await ch.declare_exchange("logos.tasks", aio_pika.ExchangeType.TOPIC, durable=True)
    q = await ch.declare_queue(f"q.{ROUTE}", durable=True)
    await q.bind(ex, ROUTE)
    await q.consume(handle)
    print(f"[{SUBSYS}] listening route '{ROUTE}' using v4 from {V4PATH}")
    return conn
