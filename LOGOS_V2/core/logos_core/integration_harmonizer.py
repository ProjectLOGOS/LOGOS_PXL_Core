"""
Integration Harmonizer - Handles semantic-axiom consistency with quarantine
Monitors drift and requires proof tokens for consistency validation
"""

import os
import sys
from typing import Any

# Add parent directory to path for imports
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from .reference_monitor import ProofGateError, ReferenceMonitor


class IntegrationHarmonizer:
    def __init__(self, config_path: str = None, drift_threshold: float = 0.7):
        if config_path is None:
            # Default to config in parent directory
            current_dir = os.path.dirname(os.path.abspath(__file__))
            config_path = os.path.join(os.path.dirname(current_dir), "configs", "config.json")
        self.reference_monitor = ReferenceMonitor(config_path)
        self.drift_threshold = drift_threshold
        self.quarantined_systems = set()

    def reconcile(self, drift_score: float, provenance: dict[str, Any]) -> dict[str, Any]:
        """
        Reconcile semantic-axiom drift with proof-gated consistency check

        Args:
            drift_score: Measure of semantic-axiom divergence (0.0 = consistent, 1.0 = fully divergent)
            provenance: Context about the source of drift

        Returns:
            Dict with reconciliation result and actions taken
        """
        system_id = provenance.get("system_id", "unknown")

        if drift_score <= self.drift_threshold:
            # Acceptable drift - no action needed
            return {
                "reconciled": True,
                "drift_score": drift_score,
                "action": "none",
                "system_id": system_id,
                "message": "Drift within acceptable threshold",
            }

        # High drift - require consistency proof
        try:
            obligation = f"BOX(consistency(semantics,axioms) and coherent_system({system_id}))"
            proof_token = self.reference_monitor.require_proof_token(obligation, provenance)

            # Consistency proven - allow continued operation
            if system_id in self.quarantined_systems:
                self.quarantined_systems.remove(system_id)

            return {
                "reconciled": True,
                "drift_score": drift_score,
                "action": "consistency_proven",
                "system_id": system_id,
                "proof_token": proof_token,
                "message": "High drift resolved via consistency proof",
            }

        except ProofGateError as e:
            # Failed to prove consistency - quarantine system
            self.quarantined_systems.add(system_id)

            return {
                "reconciled": False,
                "drift_score": drift_score,
                "action": "quarantine",
                "system_id": system_id,
                "error": str(e),
                "message": f"System {system_id} quarantined due to unresolvable semantic-axiom divergence",
            }

    def check_quarantine_status(self, system_id: str) -> dict[str, Any]:
        """Check if a system is currently quarantined"""
        is_quarantined = system_id in self.quarantined_systems

        return {
            "system_id": system_id,
            "quarantined": is_quarantined,
            "quarantined_count": len(self.quarantined_systems),
            "all_quarantined": list(self.quarantined_systems),
        }

    def attempt_quarantine_release(
        self, system_id: str, provenance: dict[str, Any]
    ) -> dict[str, Any]:
        """
        Attempt to release a system from quarantine by proving consistency
        """
        if system_id not in self.quarantined_systems:
            return {"released": False, "system_id": system_id, "error": "System is not quarantined"}

        try:
            # Require fresh consistency proof for release
            obligation = f"BOX(consistency(semantics,axioms) and rehabilitated({system_id}))"
            proof_token = self.reference_monitor.require_proof_token(obligation, provenance)

            # Release from quarantine
            self.quarantined_systems.remove(system_id)

            return {
                "released": True,
                "system_id": system_id,
                "proof_token": proof_token,
                "message": f"System {system_id} released from quarantine",
            }

        except ProofGateError as e:
            return {
                "released": False,
                "system_id": system_id,
                "error": f"Failed to prove consistency for release: {str(e)}",
            }

    def get_drift_metrics(self) -> dict[str, Any]:
        """Get current drift monitoring metrics"""
        return {
            "drift_threshold": self.drift_threshold,
            "quarantined_count": len(self.quarantined_systems),
            "quarantined_systems": list(self.quarantined_systems),
            "monitoring_active": True,
        }
