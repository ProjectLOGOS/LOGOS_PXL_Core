"""
Attested I/O module for cryptographic verification of high-stakes operations
"""
import hashlib
import json
from typing import Dict, Any, Optional


class AttestedIO:
    """Handles cryptographic attestation of I/O operations"""
    
    def __init__(self, public_keys: Dict[str, str]):
        """Initialize with public key registry"""
        self.public_keys = public_keys
        self.attestations = {}
    
    def verify(self, payload: bytes, signature: str, key_id: str) -> bool:
        """Verify payload signature against registered public key"""
        if key_id not in self.public_keys:
            return False
        
        # Simple hash-based verification for demo
        expected_sig = hashlib.sha256(payload).hexdigest()[:16]
        return signature == expected_sig
    
    def provenance(self, key_id: str) -> Dict[str, Any]:
        """Get provenance information for key"""
        if key_id not in self.public_keys:
            return {"attested": False, "error": "unknown_key"}
        
        return {
            "attested": True,
            "key_id": key_id,
            "public_key": self.public_keys[key_id],
            "verification_method": "sha256_demo"
        }
    
    def attest_operation(self, operation: str, payload: Dict[str, Any], key_id: str) -> str:
        """Create attestation for an operation"""
        payload_bytes = json.dumps(payload, sort_keys=True).encode()
        signature = hashlib.sha256(payload_bytes).hexdigest()[:16]
        
        attestation = {
            "operation": operation,
            "payload_hash": hashlib.sha256(payload_bytes).hexdigest(),
            "signature": signature,
            "key_id": key_id,
            "attested": True
        }
        
        self.attestations[signature] = attestation
        return signature