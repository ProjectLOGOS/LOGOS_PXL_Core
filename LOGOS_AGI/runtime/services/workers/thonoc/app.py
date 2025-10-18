from fastapi import FastAPI
from services.workers.common.runner import main

app = FastAPI()


@app.get("/health")
def health():
    return {"ok": True, "subsystem": "THONOC"}


@app.on_event("startup")
async def _startup():
    app.state.conn = await main()
