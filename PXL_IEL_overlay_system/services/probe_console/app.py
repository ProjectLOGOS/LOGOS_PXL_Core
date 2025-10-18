import json
import os
import pathlib

import requests
from fastapi import FastAPI, HTTPException
from fastapi.responses import HTMLResponse
from pydantic import BaseModel

ARCHON = os.getenv("ARCHON_URL", "http://archon:8000")
LOGOS = os.getenv("LOGOS_URL", "http://logos-api:8090")
EXEC = os.getenv("EXEC_URL", "http://executor:8000")

CFG = json.loads(
    (pathlib.Path(__file__).resolve().parents[2] / "configs" / "config.json").read_text(
        encoding="utf-8"
    )
)
PIN = CFG.get("expected_kernel_hash", "")

app = FastAPI()

INDEX = """
<!doctype html><html><head><meta charset="utf-8"><title>LOGOS Console</title>
<style>body{font:14px system-ui,Segoe UI,Roboto,Arial;margin:0} #top{padding:8px;border-bottom:1px solid #eee}
#hash{font-family:monospace} #io{display:flex;gap:12px;padding:12px} #out{height:60vh;overflow:auto;border:1px solid #eee;padding:8px;border-radius:8px}
#in{display:flex;gap:8px} input,button{font:14px system-ui;padding:8px}</style></head>
<body>
<div id="top">Kernel: <span id="hash"></span> · <span id="svc"></span></div>
<div id="io">
  <div style="flex:1;display:flex;flex-direction:column;gap:8px">
    <div id="out"></div>
    <div id="in">
      <input id="q" style="flex:1" placeholder="Type: crawl https://example.org  |  telos:forecast_series {&quot;horizon&quot;:12}  |  tetragnos:cluster_texts {...}  |  thonoc:construct_proof {...}">
      <button onclick="send()">Send</button>
    </div>
  </div>
</div>
<script>
const out = document.getElementById('out');
document.getElementById('hash').textContent = '(loading...)';
fetch('/status').then(r=>r.json()).then(s=>{
  document.getElementById('hash').textContent = s.kernel_hash;
  document.getElementById('svc').textContent = `ARCHON:${s.archon_ok?'ok':'down'} LOGOS:${s.logos_ok?'ok':'down'}`;
});
function append(role, text){ const d=document.createElement('div'); d.textContent = role+': '+text; out.appendChild(d); out.scrollTop=out.scrollHeight; }
async function send(){
  const q = document.getElementById('q'); const text = q.value.trim(); if(!text) return;
  append('you', text); q.value='';
  const r = await fetch('/ask',{method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({text})});
  const j = await r.json();
  append('logos', JSON.stringify(j));
}
</script>
</body></html>
"""


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
    return {"kernel_hash": PIN, "archon_ok": a, "logos_ok": l}


@app.get("/", response_class=HTMLResponse)
def index():
    return INDEX


@app.post("/ask")
def ask(inp: AskIn):
    t = inp.text.strip()
    prov = {"src": "probe_console"}
    try:
        # crawl: "crawl https://site"
        if t.lower().startswith("crawl "):
            url = t.split(None, 1)[1]
            body = {
                "action": "web_crawl",
                "args": {"url": url},
                "proof_token": {"kernel_hash": PIN},
            }
            r = requests.post(f"{EXEC}/execute", json=body, timeout=15)
            if not r.ok:
                raise HTTPException(r.status_code, r.text)
            return r.json()

        # prefixed tasks: "telos:task {json}", "tetragnos:task {json}", "thonoc:task {json}"
        for subsys in ("telos", "tetragnos", "thonoc"):
            pre = subsys + ":"
            if t.lower().startswith(pre):
                rest = t[len(pre) :].strip()
                if " " in rest:
                    task, arg = rest.split(" ", 1)
                    try:
                        payload = json.loads(arg)
                    except:
                        payload = {}
                else:
                    task, payload = rest, {}
                d = {"task_type": task, "payload": payload, "provenance": prov}
                r = requests.post(f"{ARCHON}/dispatch", json=d, timeout=15)
                if not r.ok:
                    raise HTTPException(r.status_code, r.text)
                return r.json()

        # fallback: authorize only (shows proof gating)
        auth = {"action": f"task:{t}", "state": "queued", "props": "payload", "provenance": prov}
        r = requests.post(f"{LOGOS}/authorize_action", json=auth, timeout=10)
        if not r.ok:
            raise HTTPException(403, r.text)
        return {"authorized": True, "proof_token": r.json().get("proof_token", {})}
    except HTTPException as e:
        raise e
    except Exception as e:
        raise HTTPException(500, str(e))
