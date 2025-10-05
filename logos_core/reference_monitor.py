"""
Reference Monitor - Enforces proof-gated authorization
All actuator calls and planner edges must pass through here
"""

import json
import time
import sys
import os
from typing import Dict, Any

# Add parent directory to path for imports
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from logos_core.pxl_client import PXLClient
from persistence.persistence import AuditLog

class ProofGateError(Exception):
    """Raised when proof gate fails"""
    pass

class KernelHashMismatchError(ProofGateError):
    """Raised when kernel hash doesn't match expected"""
    pass

class ReferenceMonitor:
    def __init__(self, config_path: str = None):
        if config_path is None:
            # Default to config in parent directory
            current_dir = os.path.dirname(os.path.abspath(__file__))
            config_path = os.path.join(os.path.dirname(current_dir), "configs", "config.json")
        with open(config_path, 'r') as f:
            self.config = json.load(f)
        
        self.pxl_client = PXLClient(
            self.config["pxl_prover_url"],
            self.config["timeout_ms"]
        )
        self.audit_log = AuditLog(self.config["audit_path"])
        self.expected_kernel_hash = self.config["expected_kernel_hash"]
    
    def require_proof_token(self, obligation: str, provenance: Dict[str, Any]) -> Dict[str, Any]:
        """
        Require proof token for an obligation before allowing action
        
        Args:
            obligation: BOX(formula) to be proved
            provenance: Context about who/what is requesting this proof
            
        Returns:
            Dict with proof_id and kernel_hash
            
        Raises:
            ProofGateError: If proof fails or times out
            KernelHashMismatchError: If kernel hash doesn't match expected
        """
        start_time = time.time()
        timestamp = int(start_time)
        
        # Request proof from PXL server
        proof_result = self.pxl_client.prove_box(obligation)
        proof_time_ms = int((time.time() - start_time) * 1000)
        
        # Deny on prover unreachable
        if "error" in proof_result and "Network error" in proof_result.get("error", ""):
            error_msg = f"Prover unreachable: {proof_result['error']}"
            audit_record = {
                "ts": timestamp,
                "obligation": obligation,
                "provenance": provenance,
                "decision": "DENY",
                "error": error_msg,
                "proof_time_ms": proof_time_ms,
                "proof": proof_result
            }
            self.audit_log.append(audit_record)
            raise ProofGateError(error_msg)
        
        # Check if proof succeeded
        if not proof_result.get("ok", False):
            error_msg = proof_result.get("error", "Unknown proof failure")
            
            # Log failed proof attempt
            audit_record = {
                "ts": timestamp,
                "obligation": obligation,
                "provenance": provenance,
                "decision": "DENY",
                "error": error_msg,
                "proof_time_ms": proof_time_ms,
                "proof": proof_result
            }
            self.audit_log.append(audit_record)
            
            raise ProofGateError(f"Proof failed for obligation '{obligation}': {error_msg}")
        
        # Verify kernel hash matches expected
        kernel_hash = proof_result.get("kernel_hash")
        if not kernel_hash:
            error_msg = "Missing kernel_hash in proof result"
            audit_record = {
                "ts": timestamp,
                "obligation": obligation,
                "provenance": provenance,
                "decision": "DENY",
                "error": error_msg,
                "proof_time_ms": proof_time_ms,
                "proof": proof_result
            }
            self.audit_log.append(audit_record)
            raise ProofGateError(error_msg)
            
        if kernel_hash != self.expected_kernel_hash:
            error_msg = f"Kernel hash mismatch: got {kernel_hash}, expected {self.expected_kernel_hash}"
            
            # Log kernel hash mismatch
            audit_record = {
                "ts": timestamp,
                "obligation": obligation,
                "provenance": provenance,
                "decision": "DENY",
                "error": error_msg,
                "proof_time_ms": proof_time_ms,
                "proof": proof_result
            }
            self.audit_log.append(audit_record)
            
            raise KernelHashMismatchError(error_msg)
        
        # Verify proof goal echoes the obligation (prevent mix-ups)
        proof_goal = proof_result.get("goal", "")
        if proof_goal != obligation:
            error_msg = f"Proof goal mismatch: expected '{obligation}', got '{proof_goal}'"
            audit_record = {
                "ts": timestamp,
                "obligation": obligation,
                "provenance": provenance,
                "decision": "DENY",
                "error": error_msg,
                "proof_time_ms": proof_time_ms,
                "proof": proof_result
            }
            self.audit_log.append(audit_record)
            raise ProofGateError(error_msg)
        
        # Log successful proof
        audit_record = {
            "ts": timestamp,
            "obligation": obligation,
            "provenance": provenance,
            "decision": "ALLOW",
            "proof_time_ms": proof_time_ms,
            "proof": {
                "id": proof_result.get("id"),
                "kernel_hash": kernel_hash,
                "goal": proof_result.get("goal"),
                "latency": proof_result.get("latency_ms", proof_time_ms)
            }
        }
        self.audit_log.append(audit_record)
        
        return {
            "proof_id": proof_result.get("id"),
            "kernel_hash": kernel_hash
        }
    
    def health_check(self) -> Dict[str, Any]:
        """Check health of reference monitor and PXL server"""
        pxl_health = self.pxl_client.health_check()
        
        return {
            "reference_monitor": "ok",
            "expected_kernel_hash": self.expected_kernel_hash,
            "pxl_server": pxl_health,
            "audit_log_path": self.config["audit_path"]
        }