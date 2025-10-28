"""
Simple test API for Phase 2 smoke tests
"""

import os
import sys

from flask import Flask, jsonify, request

# Add paths for imports
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from logos_core.archon_planner import ArchonPlannerGate
from logos_core.reference_monitor import ReferenceMonitor
from obdc.kernel import OBDCKernel

app = Flask(__name__)

# Initialize components
try:
    rm = ReferenceMonitor()
    planner = ArchonPlannerGate()
    obdc = OBDCKernel()
except Exception as e:
    print(f"Component initialization error: {e}")
    rm = None
    planner = None
    obdc = None


@app.route("/health", methods=["GET"])
def health():
    return jsonify(
        {
            "status": "ok",
            "components": {
                "reference_monitor": rm is not None,
                "archon_planner": planner is not None,
                "obdc_kernel": obdc is not None,
            },
            "timestamp": int(__import__("time").time()),
        }
    )


@app.route("/authorize_action", methods=["POST"])
def authorize_action():
    if not rm:
        return jsonify({"error": "reference_monitor_unavailable"}), 500

    data = request.get_json()
    action = data.get("action", "")
    state = data.get("state", "")
    props = data.get("props", "")
    provenance = data.get("provenance", {})

    # Check for DENY pattern
    if "DENY" in action.upper():
        return jsonify({"authorized": False, "reason": "explicit_deny"}), 403

    try:
        obligation = f"BOX(Good({action}) and TrueP({props}) and Coherent({state}))"
        proof_token = rm.require_proof_token(obligation, provenance)
        return jsonify(
            {
                "authorized": True,
                "obligation": obligation,
                "proof_id": proof_token.get("proof_id"),
                "kernel_hash": proof_token.get("kernel_hash"),
            }
        )
    except Exception as e:
        return jsonify({"authorized": False, "reason": str(e)}), 403


@app.route("/authorize_plan", methods=["POST"])
def authorize_plan():
    if not planner:
        return jsonify({"error": "planner_unavailable"}), 500

    data = request.get_json()
    plan_id = data.get("plan_id", "")
    steps = data.get("steps", [])
    provenance = data.get("provenance", {})

    try:
        authorized = planner.authorize_plan(steps, plan_id, provenance)
        return jsonify({"authorized": authorized, "plan_id": plan_id, "steps_count": len(steps)})
    except Exception as e:
        return jsonify({"authorized": False, "reason": str(e)}), 403


@app.route("/obdc_apply", methods=["POST"])
def obdc_apply():
    if not obdc:
        return jsonify({"error": "obdc_unavailable"}), 500

    data = request.get_json()
    name = data.get("name", "")
    x = data.get("x", 0)
    provenance = data.get("provenance", {})

    try:
        result = obdc.apply_bijection(name, x, provenance)
        return jsonify({"applied": True, "function": name, "input": x, "output": result})
    except Exception as e:
        return jsonify({"applied": False, "reason": str(e)}), 400


if __name__ == "__main__":
    from waitress import serve

    print("Starting test API on port 8090...")
    serve(app, host="127.0.0.1", port=8090)
