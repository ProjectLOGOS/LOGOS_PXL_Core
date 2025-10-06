import os

import requests
from fastapi import FastAPI, HTTPException
from pydantic import BaseModel

# Service URLs
WEB_URL = os.getenv("WEB_URL", "http://web:8000")
DB_URL = os.getenv("DB_URL", "http://db:8000")
FS_URL = os.getenv("FS_URL", "http://fs:8000")
CRAWL_URL = os.getenv("CRAWL_URL", "http://toolkit-crawl:8000")
TETRAGNOS_URL = os.getenv("TETRAGNOS_URL", "http://toolkit-tetragnos:8000")
TELOS_URL = os.getenv("TELOS_URL", "http://telos:8000")
THONOC_URL = os.getenv("THONOC_URL", "http://thonoc:8000")

app = FastAPI()


class RouteRequest(BaseModel):
    tool: str
    args: dict
    proof_token: dict


@app.get("/health")
def health():
    return {"ok": True, "service": "tool-router"}


@app.post("/route")
def route_tool(req: RouteRequest):
    """Route tool requests to appropriate service"""

    # Validate proof token
    if not req.proof_token or "kernel_hash" not in req.proof_token:
        raise HTTPException(403, "Missing proof token")

    # Route based on tool type
    if req.tool == "tetragnos":
        service_url = TETRAGNOS_URL
        endpoint = "/invoke"
    elif req.tool == "telos":
        service_url = TELOS_URL
        endpoint = "/invoke"
    elif req.tool == "thonoc":
        service_url = THONOC_URL
        endpoint = "/invoke"
    elif req.tool == "crawl" or req.tool == "web":
        service_url = CRAWL_URL
        endpoint = "/invoke"
    elif req.tool == "db":
        service_url = DB_URL
        endpoint = "/query"
    elif req.tool == "fs":
        service_url = FS_URL
        endpoint = "/operate"
    else:
        service_url = WEB_URL
        endpoint = "/process"

    try:
        # Forward request to appropriate service
        if req.tool in ["tetragnos", "telos", "thonoc", "crawl", "web"]:
            # Services with structured invoke format
            payload = {"tool": req.tool, "args": req.args, "proof_token": req.proof_token}
        else:
            payload = {"args": req.args, "proof_token": req.proof_token}

        response = requests.post(f"{service_url}{endpoint}", json=payload, timeout=15)

        if response.ok:
            return {"status": "success", "tool": req.tool, "result": response.json()}
        else:
            raise HTTPException(response.status_code, f"Tool service error: {response.text}")

    except requests.exceptions.RequestException as e:
        raise HTTPException(500, f"Tool routing failed: {str(e)}")


if __name__ == "__main__":
    import uvicorn

    print("🔧 Starting Tool Router")
    print(f"   WEB:        {WEB_URL}")
    print(f"   DB:         {DB_URL}")
    print(f"   FS:         {FS_URL}")
    print(f"   CRAWL:      {CRAWL_URL}")
    print(f"   TETRAGNOS:  {TETRAGNOS_URL}")
    uvicorn.run(app, host="0.0.0.0", port=8071)
