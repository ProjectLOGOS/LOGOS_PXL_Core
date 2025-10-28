import json

from logos_core.archon_planner import ArchonPlannerGate
from logos_core.logos_nexus import LogosNexus
from obdc.kernel import OBDCKernel


def load_config():
    with open("configs/config.json", encoding="utf-8") as f:
        return json.load(f)


if __name__ == "__main__":
    cfg = load_config()
    nexus = LogosNexus(cfg)
    gate = ArchonPlannerGate(cfg)
    obdc = OBDCKernel(cfg)

    print(nexus.handle_request("act_publish", "state_ready", "proplicit", {"src": "demo"}))
    gate.authorize_plan(["step_prepare", "step_commit"], "plan_42", {"src": "demo"})
    print(obdc.apply_bijection("f_norm", lambda x: x * 2, 5, {"src": "demo"}))
