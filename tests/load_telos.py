import json
import statistics as st
import time

import requests

N = 50
lat = []
for i in range(N):
    t = time.time()
    r = requests.post(
        "http://127.0.0.1:8075/dispatch",
        json={"task_type": "predict_outcomes", "payload": {"i": i}, "provenance": {"src": "load"}},
        timeout=10,
    )
    lat.append((time.time() - t) * 1000)
print(
    json.dumps(
        {
            "sent": N,
            "ok": sum(1 for _ in lat),
            "p50_ms": st.median(lat),
            "p95_ms": st.quantiles(lat, n=20)[18],
        }
    )
)
