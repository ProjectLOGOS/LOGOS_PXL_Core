"""
LOGOS Probe Console - Local Test Version
Run this locally for immediate testing without Docker
"""

import json
import pathlib
import urllib.parse
import urllib.request
from http.server import BaseHTTPRequestHandler, HTTPServer

# Configuration
ARCHON_URL = "http://127.0.0.1:8075"
LOGOS_URL = "http://127.0.0.1:8090"
EXEC_URL = "http://127.0.0.1:8072"
PORT = 8081

# Load kernel hash from config
try:
    config_path = pathlib.Path(__file__).resolve().parents[1] / "configs" / "config.json"
    cfg = json.loads(config_path.read_text(encoding="utf-8"))
    KERNEL_HASH = cfg.get("expected_kernel_hash", "")
except:
    KERNEL_HASH = "config_not_found"

HTML_TEMPLATE = """
<!doctype html><html><head><meta charset="utf-8"><title>LOGOS Probe Console (Local)</title>
<style>
body{font:14px system-ui,Segoe UI,Roboto,Arial;margin:0;background:#f8f9fa}
#top{padding:12px;border-bottom:2px solid #dee2e6;background:white;box-shadow:0 2px 4px rgba(0,0,0,0.05)}
#hash{font-family:monospace;color:#495057;font-size:12px} 
#status{color:#28a745;font-weight:500}
#io{display:flex;gap:16px;padding:16px;max-width:1200px;margin:0 auto} 
#out{height:65vh;overflow:auto;border:1px solid #dee2e6;padding:12px;border-radius:8px;background:white;font-family:monospace;font-size:13px}
#in{display:flex;gap:8px;margin-top:12px} 
input{flex:1;font:14px system-ui;padding:12px;border:1px solid #ced4da;border-radius:6px}
button{font:14px system-ui;padding:12px 20px;border:none;border-radius:6px;background:#007bff;color:white;cursor:pointer}
button:hover{background:#0056b3}
.msg{margin:4px 0;padding:8px;border-radius:4px}
.you{background:#e3f2fd;border-left:4px solid #2196f3}
.logos{background:#f3e5f5;border-left:4px solid #9c27b0}
.error{background:#ffebee;border-left:4px solid #f44336;color:#c62828}
#examples{margin-top:12px;padding:12px;background:#e8f5e8;border-radius:6px;font-size:13px}
#examples h4{margin:0 0 8px 0;color:#2e7d32}
#examples div{margin:4px 0;font-family:monospace;color:#1565c0;cursor:pointer}
#examples div:hover{background:#c8e6c9;padding:2px 4px;border-radius:3px}
</style></head>
<body>
<div id="top">
  <div>🔐 <strong>LOGOS Probe Console</strong> (Local Test)</div>
  <div>Kernel: <span id="hash">loading...</span></div>
  <div id="status">Services: <span id="svc">checking...</span></div>
</div>
<div id="io">
  <div style="flex:1">
    <div id="out"></div>
    <div id="in">
      <input id="q" placeholder="Enter command: crawl https://example.org  |  telos:forecast_series {&quot;horizon&quot;:12}  |  etc.">
      <button onclick="send()">Execute</button>
    </div>
    <div id="examples">
      <h4>📋 Quick Examples (click to use):</h4>
      <div onclick="setInput(this.textContent)">crawl https://example.org</div>
      <div onclick="setInput(this.textContent)">telos:predict_outcomes {"x":1,"y":2}</div>
      <div onclick="setInput(this.textContent)">tetragnos:cluster_texts {"texts":["hello","world"]}</div>
      <div onclick="setInput(this.textContent)">thonoc:construct_proof {"theorem":"A->A"}</div>
      <div onclick="setInput(this.textContent)">authorize test_action</div>
    </div>
  </div>
</div>
<script>
const out = document.getElementById('out');
const input_field = document.getElementById('q');

// Load status
fetch('/status').then(r=>r.json()).then(s=>{
  document.getElementById('hash').textContent = s.kernel_hash.substring(0,16) + '...';
  document.getElementById('svc').textContent = `ARCHON:${s.archon_ok?'✅':'❌'} LOGOS:${s.logos_ok?'✅':'❌'}`;
}).catch(()=>{
  document.getElementById('svc').textContent = 'Connection Error';
});

function setInput(text) { input_field.value = text; input_field.focus(); }

function append(role, text, isError=false){
  const d = document.createElement('div');
  d.className = `msg ${role}`;
  if(isError) d.className += ' error';
  d.textContent = `${role.toUpperCase()}: ${text}`;
  out.appendChild(d);
  out.scrollTop = out.scrollHeight;
}

async function send(){
  const text = input_field.value.trim();
  if(!text) return;
  
  append('you', text);
  input_field.value = '';
  
  try {
    const r = await fetch('/ask', {
      method: 'POST',
      headers: {'Content-Type': 'application/json'},
      body: JSON.stringify({text})
    });
    
    const j = await r.json();
    if(r.ok) {
      append('logos', JSON.stringify(j, null, 2));
    } else {
      append('error', `HTTP ${r.status}: ${JSON.stringify(j)}`, true);
    }
  } catch(e) {
    append('error', `Request failed: ${e.message}`, true);
  }
}

// Enter key support
input_field.addEventListener('keypress', (e) => {
  if(e.key === 'Enter') send();
});
</script>
</body></html>
"""


class ProbeHandler(BaseHTTPRequestHandler):
    def do_GET(self):
        if self.path == "/":
            self.send_response(200)
            self.send_header("Content-Type", "text/html")
            self.end_headers()
            self.wfile.write(HTML_TEMPLATE.encode())

        elif self.path == "/status":
            try:
                # Check ARCHON
                req = urllib.request.Request(f"{ARCHON_URL}/health")
                archon_ok = urllib.request.urlopen(req, timeout=3).getcode() == 200
            except:
                archon_ok = False

            try:
                # Check LOGOS
                req = urllib.request.Request(f"{LOGOS_URL}/health")
                logos_ok = urllib.request.urlopen(req, timeout=3).getcode() == 200
            except:
                logos_ok = False

            response = {"kernel_hash": KERNEL_HASH, "archon_ok": archon_ok, "logos_ok": logos_ok}

            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Access-Control-Allow-Origin", "*")
            self.end_headers()
            self.wfile.write(json.dumps(response).encode())
        else:
            self.send_response(404)
            self.end_headers()

    def do_POST(self):
        if self.path == "/ask":
            content_length = int(self.headers["Content-Length"])
            post_data = self.rfile.read(content_length)

            try:
                data = json.loads(post_data.decode())
                text = data.get("text", "").strip()

                result = self.process_command(text)

                self.send_response(200)
                self.send_header("Content-Type", "application/json")
                self.send_header("Access-Control-Allow-Origin", "*")
                self.end_headers()
                self.wfile.write(json.dumps(result).encode())

            except Exception as e:
                error_response = {"error": str(e)}
                self.send_response(500)
                self.send_header("Content-Type", "application/json")
                self.send_header("Access-Control-Allow-Origin", "*")
                self.end_headers()
                self.wfile.write(json.dumps(error_response).encode())
        else:
            self.send_response(404)
            self.end_headers()

    def process_command(self, text):
        """Process different types of commands"""
        provenance = {"src": "probe_console_local"}

        # Crawl command
        if text.lower().startswith("crawl "):
            url = text.split(None, 1)[1]
            body = {
                "action": "web_crawl",
                "args": {"url": url},
                "proof_token": {"kernel_hash": KERNEL_HASH},
            }
            return self.make_request(f"{EXEC_URL}/execute", body)

        # Subsystem tasks: "telos:task {json}", etc.
        for subsys in ("telos", "tetragnos", "thonoc"):
            prefix = subsys + ":"
            if text.lower().startswith(prefix):
                rest = text[len(prefix) :].strip()
                if " " in rest:
                    task, arg = rest.split(" ", 1)
                    try:
                        payload = json.loads(arg)
                    except:
                        payload = {}
                else:
                    task, payload = rest, {}

                dispatch_data = {"task_type": task, "payload": payload, "provenance": provenance}
                return self.make_request(f"{ARCHON_URL}/dispatch", dispatch_data)

        # Fallback: authorization test
        auth_data = {
            "action": f"task:{text}",
            "state": "queued",
            "props": "payload",
            "provenance": provenance,
        }
        return self.make_request(f"{LOGOS_URL}/authorize_action", auth_data)

    def make_request(self, url, data):
        """Make HTTP request to backend services"""
        try:
            req = urllib.request.Request(
                url, data=json.dumps(data).encode(), headers={"Content-Type": "application/json"}
            )
            with urllib.request.urlopen(req, timeout=15) as response:
                return json.loads(response.read().decode())
        except urllib.error.HTTPError as e:
            raise Exception(f"HTTP {e.code}: {e.read().decode()}")
        except Exception as e:
            raise Exception(f"Request failed: {str(e)}")


if __name__ == "__main__":
    print(f"🚀 Starting LOGOS Probe Console on http://localhost:{PORT}")
    print(f"📊 Kernel Hash: {KERNEL_HASH[:16]}...")
    print(f"🔗 ARCHON: {ARCHON_URL}")
    print(f"🔗 LOGOS: {LOGOS_URL}")
    print(f"🔗 EXECUTOR: {EXEC_URL}")
    print()

    server = HTTPServer(("localhost", PORT), ProbeHandler)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\n✋ Probe Console stopped")
        server.shutdown()
