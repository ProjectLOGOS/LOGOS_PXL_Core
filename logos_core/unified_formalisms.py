"""
Unified Formalisms Validator - Proof-gated authorization for all actions
Replaces heuristic allow/deny with formal proof requirements
"""

import os
import sys
from typing import Any

# Add parent directory to path for imports
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from logos_core.reference_monitor import ReferenceMonitor


class UnifiedFormalismValidator:
    def __init__(self, config_path: str = None):
        if config_path is None:
            # Default to config in parent directory
            current_dir = os.path.dirname(os.path.abspath(__file__))
            config_path = os.path.join(os.path.dirname(current_dir), "configs", "config.json")
        self.reference_monitor = ReferenceMonitor(config_path)

    def authorize(
        self, action: str, state: dict[str, Any], props: dict[str, Any], provenance: dict[str, Any]
    ) -> dict[str, Any]:
        """
        Authorize an action using proof-gated validation

        Args:
            action: The action being requested
            state: Current system state
            props: Properties/parameters of the action
            provenance: Context about the requester

        Returns:
            Dict with authorization token and proof details

        Raises:
            ProofGateError: If authorization fails
        """
        # Construct BOX obligation: Good(action) ∧ TrueP(props) ∧ Coherent(state)
        obligation = self._construct_obligation(action, state, props)

        # Require proof token from reference monitor
        proof_token = self.reference_monitor.require_proof_token(obligation, provenance)

        return {
            "authorized": True,
            "action": action,
            "proof_token": proof_token,
            "obligation": obligation,
        }

    def _construct_obligation(
        self, action: str, state: dict[str, Any], props: dict[str, Any]
    ) -> str:
        """
        Construct BOX obligation for the given action, state, and properties

        Format: BOX(Good(action) and TrueP(props) and Coherent(state))
        """
        # Sanitize action name for logical formula
        action_clean = action.replace(" ", "_").replace("-", "_")

        # Extract key properties for the obligation
        prop_assertions = []
        for key, value in props.items():
            if isinstance(value, bool):
                prop_assertions.append(f"TrueP({key})" if value else f"not TrueP({key})")
            else:
                prop_assertions.append(f"TrueP({key})")

        # Extract state coherence assertions
        state_assertions = []
        if state:
            for key in state:
                state_assertions.append(f"Coherent({key})")

        # Combine into full obligation
        parts = [f"Good({action_clean})"]
        if prop_assertions:
            parts.extend(prop_assertions)
        if state_assertions:
            parts.extend(state_assertions)

        formula = " and ".join(parts)
        return f"BOX({formula})"

    def validate_plan_step(
        self, step: dict[str, Any], provenance: dict[str, Any]
    ) -> dict[str, Any]:
        """
        Validate a single plan step requires proof of invariant preservation

        Args:
            step: The plan step to validate
            provenance: Context about the plan/planner

        Returns:
            Dict with validation result and proof token
        """
        step_id = step.get("id", "unknown")
        obligation = f"BOX(preserves_invariants({step_id}))"

        proof_token = self.reference_monitor.require_proof_token(obligation, provenance)

        return {
            "step_valid": True,
            "step_id": step_id,
            "proof_token": proof_token,
            "obligation": obligation,
        }

    def validate_plan_goal(
        self, plan_id: str, goal: str, provenance: dict[str, Any]
    ) -> dict[str, Any]:
        """
        Validate plan-level goal using DIAMOND modality

        Args:
            plan_id: Identifier for the plan
            goal: The goal to be achieved
            provenance: Context about the plan/planner

        Returns:
            Dict with validation result and proof token
        """
        # Plan-level obligation: BOX(DIAMOND(Goal(plan_id)))
        obligation = f"BOX(DIAMOND(Goal({plan_id})))"

        proof_token = self.reference_monitor.require_proof_token(obligation, provenance)

        return {
            "plan_valid": True,
            "plan_id": plan_id,
            "goal": goal,
            "proof_token": proof_token,
            "obligation": obligation,
        }
