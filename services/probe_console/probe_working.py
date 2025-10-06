import requests
from fastapi import FastAPI
from fastapi.responses import HTMLResponse
from pydantic import BaseModel

# Working services only
ARCHON = "http://localhost:8075"

app = FastAPI()


class AskIn(BaseModel):
    text: str


@app.get("/status")
def status():
    try:
        a = requests.get(f"{ARCHON}/health", timeout=3).ok
    except:
        a = False
    return {"archon_ok": a, "service": "probe_console_working"}


@app.get("/")
def index():
    return HTMLResponse(
        """
    <!doctype html><html><head><title>LOGOS Console - Working</title></head>
    <body>
    <h1>LOGOS Console - ARCHON Test</h1>
    <div id="status">Loading...</div>
    <br><br>
    <input type="text" id="command" placeholder="Enter task command (e.g., 'test_task')" style="width:400px">
    <button onclick="sendCommand()">Send to ARCHON</button>
    <div id="result" style="margin-top:20px; padding:10px; border:1px solid #ccc; min-height:100px;"></div>
    
    <script>
    fetch('/status').then(r=>r.json()).then(s=>{
      document.getElementById('status').innerHTML = 
        `ARCHON: ${s.archon_ok ? 'OK ✅' : 'DOWN ❌'}`;
    });
    
    async function sendCommand() {
      const cmd = document.getElementById('command').value.trim();
      if (!cmd) return;
      
      document.getElementById('result').innerHTML = 'Sending...';
      
      try {
        const response = await fetch('/ask', {
          method: 'POST',
          headers: {'Content-Type': 'application/json'},
          body: JSON.stringify({text: cmd})
        });
        const result = await response.json();
        document.getElementById('result').innerHTML = 
          '<pre>' + JSON.stringify(result, null, 2) + '</pre>';
      } catch(e) {
        document.getElementById('result').innerHTML = 'Error: ' + e.message;
      }
    }
    </script>
    </body></html>
    """
    )


@app.post("/ask")
def ask(inp: AskIn):
    cmd = inp.text.strip()

    try:
        # Send directly to ARCHON dispatch
        payload = {
            "task_type": cmd,
            "payload": {"command": cmd},
            "provenance": {"src": "probe_working", "timestamp": "now"},
        }

        r = requests.post(f"{ARCHON}/dispatch", json=payload, timeout=15)

        if r.ok:
            return {"success": True, "archon_response": r.json()}
        else:
            return {"success": False, "error": f"ARCHON returned {r.status_code}: {r.text}"}

    except Exception as e:
        return {"success": False, "error": str(e)}


if __name__ == "__main__":
    import uvicorn

    print("Starting Working LOGOS Probe Console")
    print(f"ARCHON: {ARCHON}")
    uvicorn.run(app, host="127.0.0.1", port=8083)
