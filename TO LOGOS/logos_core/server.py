import json
import pathlib
import sys
import time

from fastapi import FastAPI, HTTPException
from pydantic import BaseModel

# Add audit system
sys.path.append(str(pathlib.Path(__file__).parent.parent))
from audit.audit_system import audit

app = FastAPI()


def _cfg():
    p = pathlib.Path(__file__).resolve().parents[1] / "configs" / "config.json"
    return json.loads(p.read_text(encoding="utf-8"))


CFG = _cfg()
PIN = CFG.get("expected_kernel_hash", "")

# Try real gate
RM = None
try:
    from logos_core.logos_nexus import LogosNexus

    RM = LogosNexus(CFG).validator.rm
except Exception:
    RM = None


class AuthIn(BaseModel):
    action: str
    state: str
    props: str
    provenance: dict = {}


@app.get("/health")
def health():
    return {"ok": True, "kernel_hash": PIN, "ts": int(time.time() * 1000)}


def _obligation(a, s, p):
    return f"Good({a}) and TrueP({p}) and Coherent({s})"


# Minimal privative deny set while RM is unavailable
def _privative_deny(action: str) -> bool:
    bad = (
        "forbidden",
        "delete",
        "overwrite",
        "exfiltrate",
        "unsafe_write",
        "rm ",
        "drop table",
        "shutdown",
    )
    return any(k in action.lower() for k in bad)


@app.post("/authorize_action")
def authorize_action(inp: AuthIn):
    obl = _obligation(inp.action, inp.state, inp.props)

    # Try ReferenceMonitor first
    if RM:
        try:
            tok = RM.require_proof_token(
                obl, dict(inp.provenance, action=inp.action, state=inp.state)
            )
            # Log successful authorization
            try:
                audit.log_decision(
                    inp.action, "authorized", tok, {"obligation": obl, "source": "ReferenceMonitor"}
                )
            except Exception as e:
                print(f"Audit logging error: {e}")
            return {"authorized": True, "proof_token": tok}
        except Exception as e:
            # Log denial
            try:
                audit.log_decision(
                    inp.action,
                    "denied",
                    None,
                    {"reason": str(e), "obligation": obl, "source": "ReferenceMonitor"},
                )
            except Exception as audit_err:
                print(f"Audit logging error: {audit_err}")
            raise HTTPException(403, str(e))

    # Fallback policy: deny unless action in known-safe tests AND passes privative screen
    safe = {"task:predict_outcomes", "task:cluster_texts", "task:construct_proof"}
    if _privative_deny(inp.action) or inp.action not in safe:
        # Log denial
        try:
            reason = "privative_deny" if _privative_deny(inp.action) else "not_in_allowlist"
            audit.log_decision(
                inp.action,
                "denied",
                None,
                {"reason": reason, "obligation": obl, "source": "fallback_policy"},
            )
        except Exception as e:
            print(f"Audit logging error: {e}")
        raise HTTPException(403, "deny-by-default (RM unavailable)")

    # Authorized by fallback
    proof_token = {"id": "fallback", "kernel_hash": PIN, "obligation": obl}
    try:
        audit.log_decision(
            inp.action,
            "authorized",
            proof_token,
            {"obligation": obl, "source": "fallback_allowlist"},
        )
    except Exception as e:
        print(f"Audit logging error: {e}")

    return {"authorized": True, "proof_token": proof_token}


@app.get("/health")
def health():
    return {"ok": True}
