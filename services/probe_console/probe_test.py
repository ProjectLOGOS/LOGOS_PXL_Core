import requests
from fastapi import FastAPI
from fastapi.responses import HTMLResponse
from pydantic import BaseModel

# Use localhost for local testing
ARCHON = "http://localhost:8075"
LOGOS = "http://localhost:8090"
EXEC = "http://localhost:8072"
PIN = "test_hash"

app = FastAPI()


class AskIn(BaseModel):
    text: str


@app.get("/status")
def status():
    try:
        a = requests.get(f"{ARCHON}/health", timeout=3).ok
    except:
        a = False
    try:
        l = requests.get(f"{LOGOS}/health", timeout=3).ok
    except:
        l = False
    try:
        e = requests.get(f"{EXEC}/health", timeout=3).ok
    except:
        e = False
    return {"kernel_hash": PIN, "archon_ok": a, "logos_ok": l, "exec_ok": e}


@app.get("/")
def index():
    return HTMLResponse(
        """
    <!doctype html><html><head><title>LOGOS Console Test</title></head>
    <body>
    <h1>LOGOS Console Test</h1>
    <div id="status">Loading...</div>
    <script>
    fetch('/status').then(r=>r.json()).then(s=>{
      document.getElementById('status').innerHTML = 
        `Kernel: ${s.kernel_hash}<br>
         ARCHON: ${s.archon_ok ? 'OK' : 'DOWN'}<br>
         LOGOS: ${s.logos_ok ? 'OK' : 'DOWN'}<br>
         EXEC: ${s.exec_ok ? 'OK' : 'DOWN'}`;
    });
    </script>
    </body></html>
    """
    )


@app.post("/ask")
def ask(inp: AskIn):
    t = inp.text.strip()

    # Test ARCHON dispatch
    if t.lower().startswith("test archon"):
        try:
            d = {"task_type": "test", "payload": {}, "provenance": {"src": "probe_test"}}
            r = requests.post(f"{ARCHON}/dispatch", json=d, timeout=15)
            return {"status": r.status_code, "response": r.text}
        except Exception as e:
            return {"error": str(e)}

    # Test LOGOS authorize
    if t.lower().startswith("test logos"):
        try:
            auth = {
                "action": "task:test",
                "state": "queued",
                "props": "payload",
                "provenance": {"src": "probe_test"},
            }
            r = requests.post(f"{LOGOS}/authorize_action", json=auth, timeout=10)
            return {"status": r.status_code, "response": r.text}
        except Exception as e:
            return {"error": str(e)}

    return {"message": "Unknown command. Try 'test archon' or 'test logos'"}


if __name__ == "__main__":
    import uvicorn

    print("Starting LOGOS Probe Console Test")
    print(f"ARCHON: {ARCHON}")
    print(f"LOGOS:  {LOGOS}")
    print(f"EXEC:   {EXEC}")
    uvicorn.run(app, host="127.0.0.1", port=8082)
