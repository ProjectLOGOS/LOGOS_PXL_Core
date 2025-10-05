
from policies.privative_policies import obligation_for
from logos_core.reference_monitor import ReferenceMonitor

class UnifiedFormalismValidator:
    def __init__(self, config: dict):
        self.rm = ReferenceMonitor(config)

    def authorize(self, action: str, state: str, props: str, provenance: dict) -> dict:
        phi = obligation_for(action, state, props)
        return self.rm.require_proof_token(phi, provenance)
