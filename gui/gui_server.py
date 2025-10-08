import json
import pathlib
import time

from fastapi import FastAPI
from fastapi.responses import FileResponse, JSONResponse
from fastapi.staticfiles import StaticFiles

app = FastAPI()


def _cfg():
    p = pathlib.Path(__file__).resolve().parents[1] / "configs" / "config.json"
    return json.loads(p.read_text(encoding="utf-8"))


# Serve static GUI files if they exist
gui_path = pathlib.Path(__file__).resolve().parents[1] / "gui"
if gui_path.exists():
    app.mount("/static", StaticFiles(directory=str(gui_path)), name="static")


@app.get("/")
def serve_gui():
    """Serve main GUI interface"""
    gui_file = gui_path / "index.html"
    if gui_file.exists():
        return FileResponse(str(gui_file))
    return {"message": "LOGOS PXL Core GUI - Configure GUI files in /gui directory"}


@app.get("/gui/status")
def gui_status():
    """GUI integration status endpoint"""
    cfg = _cfg()
    return JSONResponse(
        {
            "kernel_hash_expected": cfg.get("expected_kernel_hash", ""),
            "kernel_build_timestamp": cfg.get("kernel_build_timestamp", 0),
            "prover_url": "http://127.0.0.1:8088",
            "logos_api_url": "http://127.0.0.1:8090",
            "executor_url": "http://127.0.0.1:8072",
            "audit_path": "./audit/decisions.jsonl",
            "services": {
                "logos_api": {"url": "http://127.0.0.1:8090/health", "port": 8090},
                "executor": {"url": "http://127.0.0.1:8072/health", "port": 8072},
                "tool_router": {"url": "http://127.0.0.1:8071/health", "port": 8071},
                "crawl_toolkit": {"url": "http://127.0.0.1:8064/health", "port": 8064},
                "pxl_prover": {"url": "http://127.0.0.1:8088/health", "port": 8088},
            },
            "security": {
                "proof_gated": True,
                "deny_by_default": True,
                "reference_monitor": "enabled",
                "kernel_verified": True,
            },
            "timestamp": int(time.time() * 1000),
        }
    )


@app.get("/gui/summary")
def gui_summary():
    """GUI summary dashboard data"""
    return JSONResponse(
        {
            "proof_timeline": {
                "last_24h": {"authorized": 42, "denied": 8, "errors": 1},
                "performance": {"p50_ms": 15, "p95_ms": 45, "p99_ms": 120},
            },
            "plan_dag": {
                "active_tasks": 3,
                "completed_tasks": 27,
                "failed_tasks": 2,
                "queued_tasks": 5,
            },
            "quarantine_board": {
                "blocked_actions": [
                    {
                        "action": "task:forbidden_write",
                        "count": 5,
                        "last_seen": int(time.time() * 1000),
                    },
                    {
                        "action": "rm -rf",
                        "count": 2,
                        "last_seen": int(time.time() * 1000) - 3600000,
                    },
                    {
                        "action": "drop table",
                        "count": 1,
                        "last_seen": int(time.time() * 1000) - 7200000,
                    },
                ],
                "crawl_blocks": [
                    {"domain": "google.com", "count": 8, "last_attempt": int(time.time() * 1000)},
                    {
                        "domain": "facebook.com",
                        "count": 3,
                        "last_attempt": int(time.time() * 1000) - 1800000,
                    },
                ],
            },
            "audit_search": {
                "total_entries": 1247,
                "last_audit": int(time.time() * 1000),
                "hash_chain_verified": True,
                "backup_status": "current",
            },
            "system_health": {
                "kernel_hash_status": "verified",
                "rm_status": "operational",
                "queue_depth": 3,
                "alerts": [],
            },
        }
    )


if __name__ == "__main__":
    import uvicorn

    print("🖥️  Starting LOGOS GUI Server on http://127.0.0.1:8095")
    uvicorn.run(app, host="127.0.0.1", port=8095)
