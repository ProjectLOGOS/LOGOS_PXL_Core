import hashlib
from typing import Any

from fastapi import FastAPI, HTTPException
from pydantic import BaseModel

# heavy deps
from sentence_transformers import SentenceTransformer
from sklearn.cluster import KMeans

app = FastAPI()
_model = SentenceTransformer("all-MiniLM-L6-v2")  # cached under model_cache if mounted


class Invoke(BaseModel):
    tool: str
    args: dict[str, Any]
    proof_token: dict[str, Any]


@app.get("/health")
def health():
    return {"ok": True, "subsystem": "TETRAGNOS"}


def _hash(x: str) -> str:
    return hashlib.sha256(x.encode("utf-8")).hexdigest()


@app.post("/invoke")
def invoke(t: Invoke):
    if not t.proof_token or "kernel_hash" not in t.proof_token:
        raise HTTPException(403, "missing proof token")
    if t.tool != "tetragnos":
        raise HTTPException(400, "bad tool route")

    op = t.args.get("op")
    if op == "cluster_texts":
        texts: list[str] = t.args.get("texts") or []
        if not texts or not isinstance(texts, list):
            raise HTTPException(400, "texts[] required")
        k = int(t.args.get("k") or max(1, min(8, len(texts) // 2 or 1)))
        embs = _model.encode(texts).tolist()
        labels = KMeans(n_clusters=k, n_init="auto", random_state=0).fit(embs).labels_.tolist()
        items = [
            {"text": s, "hash": _hash(s), "cluster": int(c)}
            for s, c in zip(texts, labels, strict=False)
        ]
        return {"ok": True, "op": "cluster_texts", "k": k, "items": items}

    # reserve additional ops: "semantic_map", "similarity", etc.
    raise HTTPException(400, "unsupported op")
