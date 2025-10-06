from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
from typing import Dict, Any
from z3 import Bool, Not, Implies, And, Or, Solver, is_true, Tactic, Goal

app = FastAPI()

class Invoke(BaseModel):
    tool: str
    args: Dict[str, Any]
    proof_token: Dict[str, Any]

@app.get("/health")
def health(): return {"ok": True, "subsystem": "THONOC"}

def _mk(formula:str):
    # Minimal parser for forms like "A->A", "A->(A|B)", "(A&B)->A"
    # Vars: uppercase letters; ops: ->, &, |, ! ; parens allowed.
    s = formula.replace(" ", "")
    vars = sorted({c for c in s if c.isalpha() and c.isupper()})
    env = {v: Bool(v) for v in vars}
    def parse(expr):
        # recursive, left-to-right for simplicity; not full precedence
        # handle negation
        if expr.startswith("!"): return Not(parse(expr[1:]))
        # strip outer parens
        if expr.startswith("(") and expr.endswith(")"):
            # naive balance check
            bal=0; ok=True
            for i,ch in enumerate(expr):
                if ch=="(": bal+=1
                if ch==")": bal-=1
                if bal==0 and i<len(expr)-1: ok=False; break
            if ok: return parse(expr[1:-1])
        # binary ops by priority
        for op,f in (("->", Implies), ("&", And), ("|", Or)):
            # split on the first op at top-level
            bal=0
            for i in range(len(expr)):
                ch=expr[i]
                if ch=="(": bal+=1
                elif ch==")": bal-=1
                else:
                    if bal==0 and expr[i:].startswith(op):
                        left = parse(expr[:i])
                        right = parse(expr[i+len(op):])
                        return f(left, right)
        # variable
        if expr in env: return env[expr]
        raise ValueError("bad formula")
    return parse(s), env

@app.post("/invoke")
def invoke(t: Invoke):
    if not t.proof_token or "kernel_hash" not in t.proof_token:
        raise HTTPException(403, "missing proof token")
    if t.tool != "thonoc": raise HTTPException(400, "bad tool route")

    op = t.args.get("op")
    if op == "construct_proof":
        formula = t.args.get("formula")
        if not formula: raise HTTPException(400, "formula required, e.g., 'A->A'")
        try:
            phi, _ = _mk(formula)
            # Prove tautology by showing ¬phi is unsat
            s = Solver(); s.add(Not(phi))
            is_taut = (s.check().name == "unsat")
            proof = None
            try:
                # Try to get a proof object if available via tactics
                g = Goal(); g.add(Not(phi)); pr = Tactic("smt").apply(g)
                proof = str(pr.as_expr())
            except Exception:
                proof = "proof-sketch: unsat(¬φ)"
            return {"ok": True, "op":"construct_proof", "formula": formula, "tautology": is_taut, "proof": proof}
        except Exception as e:
            raise HTTPException(400, f"parse/prove error: {e}")

    raise HTTPException(400, "unsupported op")