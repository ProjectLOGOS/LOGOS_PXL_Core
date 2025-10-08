from logos_core.reference_monitor import ReferenceMonitor


class IntegrationHarmonizer:
    def __init__(self, config: dict, threshold: float = 0.5):
        self.rm = ReferenceMonitor(config)
        self.threshold = threshold

    def reconcile(self, drift_score: float, provenance: dict):
        if drift_score <= self.threshold:
            return {"status": "OK"}
        self.rm.require_proof_token(
            "consistency(semantics, axioms)", dict(provenance, drift=drift_score)
        )
        return {"status": "QUARANTINE_CLEARED"}
