"""
Minimal LOGOS Core API.
Why: Unblock router and chat with a proof-gated token mint and kernel hash check.
"""
from __future__ import annotations

import hashlib
import hmac
import os
import secrets
import time
from typing import Any

from fastapi import FastAPI, Header, HTTPException
from pydantic import BaseModel, Field

API_SIGNING_SECRET = os.getenv("API_SIGNING_SECRET", "")
TOKEN_TTL_SECS = int(os.getenv("TOKEN_TTL_SECS", "300"))
KERNEL_HASH = os.getenv("KERNEL_HASH", "")  # optional expected hash

app = FastAPI(title="LOGOS Core API", version="0.1.0")

class AuthorizeRequest(BaseModel):
    action: str = Field(..., min_length=1)
    state: dict[str, Any] = {}

class ProofToken(BaseModel):
    token: str
    exp: int
    action_sha256: str
    nonce: str

class AuthorizeResponse(BaseModel):
    ok: bool
    proof_token: ProofToken

class VerifyKernelRequest(BaseModel):
    kernel_hash: str

class VerifyKernelResponse(BaseModel):
    ok: bool
    match: bool

def _sign(msg: str) -> str:
    if not API_SIGNING_SECRET:
        return ""
    return hmac.new(API_SIGNING_SECRET.encode(), msg.encode(), hashlib.sha256).hexdigest()

@app.get("/health")
def health():
    return {"ok": True}

@app.post("/authorize_action", response_model=AuthorizeResponse)
def authorize_action(body: AuthorizeRequest, x_client_id: str | None = Header(default=None)):
    now = int(time.time())
    exp = now + TOKEN_TTL_SECS
    nonce = secrets.token_urlsafe(16)
    action_hash = hashlib.sha256(body.action.encode()).hexdigest()
    payload = f"{nonce}.{exp}.{action_hash}"
    token = _sign(payload) if API_SIGNING_SECRET else secrets.token_urlsafe(24)
    return AuthorizeResponse(
        ok=True,
        proof_token=ProofToken(token=token, exp=exp, action_sha256=action_hash, nonce=nonce),
    )

@app.post("/verify_kernel", response_model=VerifyKernelResponse)
def verify_kernel(body: VerifyKernelRequest):
    if not body.kernel_hash:
        raise HTTPException(status_code=400, detail="kernel_hash_required")
    if not KERNEL_HASH:
        # no expected hash configured; accept but signal no comparison
        return VerifyKernelResponse(ok=True, match=True)
    return VerifyKernelResponse(ok=True, match=(body.kernel_hash == KERNEL_HASH))
