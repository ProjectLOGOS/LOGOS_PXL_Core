import json
import pathlib

import requests
from fastapi import FastAPI
from fastapi.responses import HTMLResponse
from pydantic import BaseModel

# Service endpoints
ARCHON = "http://localhost:8075"
LOGOS = "http://localhost:8090"
EXEC = "http://localhost:8072"

# Get kernel hash
try:
    CFG = json.loads(
        (pathlib.Path(__file__).resolve().parents[2] / "configs" / "config.json").read_text(
            encoding="utf-8"
        )
    )
    PIN = CFG.get("expected_kernel_hash", "")
except:
    PIN = "fallback_hash"

app = FastAPI()


class AskIn(BaseModel):
    text: str


@app.get("/status")
def status():
    try:
        logos_ok = requests.get(f"{LOGOS}/health", timeout=3).ok
    except:
        logos_ok = False
    try:
        exec_ok = requests.get(f"{EXEC}/health", timeout=3).ok
    except:
        exec_ok = False
    return {"kernel_hash": PIN, "logos_ok": logos_ok, "exec_ok": exec_ok}


@app.get("/")
def index():
    return HTMLResponse(
        """
    <!doctype html><html><head><title>LOGOS Probe Console - WORKING</title>
    <style>body{font:14px Arial;margin:20px}#status{background:#f0f0f0;padding:10px;border-radius:5px;margin-bottom:20px}
    #cmd{width:60%;padding:10px;margin-right:10px}button{padding:10px 20px}#result{margin-top:20px;padding:15px;border:1px solid #ddd;min-height:200px;background:#fafafa;border-radius:5px}
    .success{color:green}.error{color:red}.info{color:blue}</style></head>
    <body>
    <h1>🚀 LOGOS Probe Console - OPERATIONAL</h1>
    <div id="status">Loading system status...</div>
    
    <h3>Test Commands:</h3>
    <ul>
        <li><code>test logos</code> - Test LOGOS authorization</li>
        <li><code>test exec</code> - Test Executor health</li> 
        <li><code>authorize [action]</code> - Get proof token</li>
    </ul>
    
    <input type="text" id="cmd" placeholder="Enter command (e.g., 'test logos')" value="test logos">
    <button onclick="sendCommand()">Execute</button>
    <div id="result">Ready for commands...</div>
    
    <script>
    fetch('/status').then(r=>r.json()).then(s=>{
      document.getElementById('status').innerHTML = 
        `<strong>System Status:</strong><br>
         🔒 Kernel Hash: ${s.kernel_hash.substring(0,16)}...<br>
         📡 LOGOS API: <span class="${s.logos_ok?'success':'error'}">${s.logos_ok?'✅ ONLINE':'❌ OFFLINE'}</span><br>  
         ⚡ Executor: <span class="${s.exec_ok?'success':'error'}">${s.exec_ok?'✅ ONLINE':'❌ OFFLINE'}</span>`;
    });
    
    async function sendCommand() {
      const cmd = document.getElementById('cmd').value.trim();
      if (!cmd) return;
      
      document.getElementById('result').innerHTML = '<div class="info">⏳ Processing...</div>';
      
      try {
        const response = await fetch('/ask', {
          method: 'POST',
          headers: {'Content-Type': 'application/json'},
          body: JSON.stringify({text: cmd})
        });
        const result = await response.json();
        
        let html = '<div class="success">✅ Success</div>';
        html += '<pre>' + JSON.stringify(result, null, 2) + '</pre>';
        document.getElementById('result').innerHTML = html;
      } catch(e) {
        document.getElementById('result').innerHTML = 
          '<div class="error">❌ Error: ' + e.message + '</div>';
      }
    }
    </script>
    </body></html>
    """
    )


@app.post("/ask")
def ask(inp: AskIn):
    cmd = inp.text.strip().lower()

    # Test LOGOS authorization
    if cmd.startswith("test logos") or cmd.startswith("authorize"):
        action = cmd.replace("test logos", "").replace("authorize", "").strip() or "probe_test"
        try:
            auth_payload = {
                "action": f"task:{action}",
                "state": "active",
                "props": "verified",
                "provenance": {"src": "probe_console", "cmd": cmd},
            }
            r = requests.post(f"{LOGOS}/authorize_action", json=auth_payload, timeout=10)
            if r.ok:
                return {"test": "LOGOS authorization", "status": "SUCCESS", "response": r.json()}
            else:
                return {"test": "LOGOS authorization", "status": "FAILED", "error": r.text}
        except Exception as e:
            return {"test": "LOGOS authorization", "status": "ERROR", "error": str(e)}

    # Test Executor
    elif cmd.startswith("test exec"):
        try:
            r = requests.get(f"{EXEC}/health", timeout=5)
            return {"test": "Executor health", "status": "SUCCESS", "response": r.json()}
        except Exception as e:
            return {"test": "Executor health", "status": "ERROR", "error": str(e)}

    # Default response
    else:
        return {
            "message": "Unknown command",
            "available_commands": [
                "test logos - Test authorization flow",
                "test exec - Test executor health",
                "authorize [action] - Get proof token for action",
            ],
        }


if __name__ == "__main__":
    import uvicorn

    print("🚀 Starting LOGOS Probe Console - Final Working Version")
    print(f"📡 LOGOS:  {LOGOS}")
    print(f"⚡ EXEC:   {EXEC}")
    print(f"🔒 Hash:   {PIN[:16]}...")
    uvicorn.run(app, host="127.0.0.1", port=8084)
