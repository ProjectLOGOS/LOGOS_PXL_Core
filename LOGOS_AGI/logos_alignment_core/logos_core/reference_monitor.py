import time

from logos_core.pxl_client import PXLClient
from persistence.persistence import AuditLog


class ReferenceMonitor:
    def __init__(self, config: dict):
        self.client = PXLClient(config["pxl_prover_url"], config.get("timeout_ms", 2000))
        self.expected_kernel_hash = config["expected_kernel_hash"]
        self.audit = AuditLog(config["audit_path"])

    def require_proof_token(self, obligation: str, provenance: dict) -> dict:
        ok, proof = self.client.prove_box(obligation)
        record = {
            "ts": int(time.time() * 1000),
            "obligation": obligation,
            "provenance": provenance,
            "decision": "ALLOW" if ok else "DENY",
            "proof": proof,
        }
        self.audit.append(record)
        if not ok:
            raise PermissionError("obligation failed or undecided")
        kernel_hash = proof.get("kernel_hash", "UNKNOWN")
        if self.expected_kernel_hash != "DEADBEEF" and kernel_hash != self.expected_kernel_hash:
            raise PermissionError("kernel hash mismatch")
        return {"proof_id": proof.get("id", "unknown"), "kernel_hash": kernel_hash}
