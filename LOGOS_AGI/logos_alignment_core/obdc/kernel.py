from logos_core.reference_monitor import ReferenceMonitor


class OBDCKernel:
    def __init__(self, config: dict):
        self.rm = ReferenceMonitor(config)

    def apply_bijection(self, name, f, x, provenance: dict):
        phi = f"preserves_good({name},{x}) and preserves_coherence({name})"
        self.rm.require_proof_token(phi, dict(provenance, map=name))
        return f(x)

    def commute(self, g_name, h_name, g, h, s, provenance: dict):
        phi = f"commutes({g_name},{h_name}) and preserves_coherence_chain({g_name},{h_name})"
        self.rm.require_proof_token(phi, dict(provenance, g=g_name, h=h_name))
        return g(h(s))
