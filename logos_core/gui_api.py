import json
import pathlib

from fastapi import APIRouter

router = APIRouter()


def _cfg():
    p = pathlib.Path(__file__).resolve().parents[1] / "configs" / "config.json"
    return json.loads(p.read_text(encoding="utf-8"))


@router.get("/gui/status")
def status():
    cfg = _cfg()
    return {
        "kernel_hash_expected": cfg.get("expected_kernel_hash"),
        "prover_url": cfg.get("pxl_prover_url"),
        "audit_path": cfg.get("audit_path"),
    }
