from fastapi import FastAPI
import asyncio, os
from services.workers.common.runner import main
app = FastAPI()
@app.get("/health")
def health(): return {"ok": True, "subsystem":"THONOC"}
@app.on_event("startup")
async def _startup(): app.state.conn = await main()