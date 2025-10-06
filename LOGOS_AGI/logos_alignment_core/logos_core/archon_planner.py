from logos_core.reference_monitor import ReferenceMonitor
from policies.privative_policies import preserves_invariants


class ArchonPlannerGate:
    def __init__(self, config: dict):
        self.rm = ReferenceMonitor(config)
        self.client = self.rm.client

    def check_step(self, step: str, provenance: dict):
        phi = preserves_invariants(step)
        self.rm.require_proof_token(phi, dict(provenance, step=step))

    def check_plan_reachability(self, plan_id: str) -> bool:
        ok, _ = self.client.prove_box(f"DIAMOND(Goal({plan_id}))")
        return ok

    def authorize_plan(self, steps, plan_id: str, provenance: dict):
        for s in steps:
            self.check_step(s, provenance)
        if not self.check_plan_reachability(plan_id):
            raise ValueError("plan not reachable")
        return True
