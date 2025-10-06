from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
import os, requests
import traceback

ROUTER = os.getenv("TOOL_ROUTER_URL","http://127.0.0.1:8071")

app = FastAPI()

class ExecReq(BaseModel):
    action:str; args:dict; proof_token:dict

@app.get("/health")
def health(): return {"ok": True, "router": ROUTER}

@app.post("/execute")
def execute(x: ExecReq):
    try:
        print(f"DEBUG: Received action: {x.action}")
        print(f"DEBUG: Router URL: {ROUTER}")
        
        if not x.proof_token or "kernel_hash" not in x.proof_token:
            raise HTTPException(403, "missing proof token")
            
        # Route actions to appropriate tools
        m = x.action.lower()
        if "cluster_texts" in m or "tetragnos" in m:
            tool = "tetragnos"
        elif "crawl" in m:
            tool = "crawl"
        elif m.startswith("http"):
            tool = "web"
        elif "write" in m:
            tool = "fs"
        else:
            tool = "db"
            
        print(f"DEBUG: Selected tool: {tool}")
        
        route_payload = {"tool": tool, "args": x.args, "proof_token": x.proof_token}
        print(f"DEBUG: Route payload: {route_payload}")
        
        r = requests.post(f"{ROUTER}/route", json=route_payload, timeout=15)
        print(f"DEBUG: Router response status: {r.status_code}")
        print(f"DEBUG: Router response text: {r.text}")
        
        if not r.ok: 
            raise HTTPException(r.status_code, f"Router error: {r.text}")
            
        return {"status":"OK","result": r.json()}
        
    except Exception as e:
        print(f"DEBUG: Exception occurred: {str(e)}")
        print(f"DEBUG: Traceback: {traceback.format_exc()}")
        raise HTTPException(500, f"Execution failed: {str(e)}")

if __name__ == "__main__":
    import uvicorn
    print(f"🔧 Starting DEBUG Executor")
    print(f"   Router: {ROUTER}")
    uvicorn.run(app, host="127.0.0.1", port=8072)