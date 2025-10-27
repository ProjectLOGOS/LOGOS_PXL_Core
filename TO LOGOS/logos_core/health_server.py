
from fastapi import FastAPI
import requests
import time
from datetime import datetime

app = FastAPI(title="LOGOS Health Monitor")

@app.get("/")
async def health_dashboard():
    services = {
        "LOGOS API": "http://localhost:8090/health",
        "Demo Interface": "http://localhost:8080/health"
    }

    status = {}
    for name, url in services.items():
        try:
            response = requests.get(url, timeout=5)
            status[name] = {
                "status": "healthy" if response.status_code == 200 else "unhealthy",
                "response_time": response.elapsed.total_seconds() * 1000,
                "last_check": datetime.now().isoformat()
            }
        except Exception as e:
            status[name] = {
                "status": "unreachable",
                "error": str(e),
                "last_check": datetime.now().isoformat()
            }

    overall_health = all(s["status"] == "healthy" for s in status.values())

    return {
        "overall_health": "healthy" if overall_health else "degraded",
        "services": status,
        "timestamp": datetime.now().isoformat()
    }

if __name__ == "__main__":
    import uvicorn
    uvicorn.run(app, host="127.0.0.1", port=8099)
