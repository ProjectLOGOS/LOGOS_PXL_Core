"""
LOGOS Nexus - Main request handler with proof-gated authorization
All requests require proof tokens before processing
"""

import os
import sys
from typing import Any

# Add parent directory to path for imports
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from logos_core.reference_monitor import ProofGateError
from logos_core.unified_formalisms import UnifiedFormalismValidator


class LogosNexus:
    def __init__(self, config_path: str = None):
        if config_path is None:
            # Default to config in parent directory
            current_dir = os.path.dirname(os.path.abspath(__file__))
            config_path = os.path.join(os.path.dirname(current_dir), "configs", "config.json")
        self.validator = UnifiedFormalismValidator(config_path)

    def handle_request(
        self, request_type: str, payload: dict[str, Any], provenance: dict[str, Any]
    ) -> dict[str, Any]:
        """
        Handle incoming request with proof-gated authorization

        Args:
            request_type: Type of request (e.g., "action", "query", "plan")
            payload: Request payload with parameters
            provenance: Context about the requester

        Returns:
            Dict with response and proof token
        """
        try:
            # Authorize the request through unified formalism validator
            state = payload.get("state", {})
            props = payload.get("properties", {})

            authorization = self.validator.authorize(
                action=request_type, state=state, props=props, provenance=provenance
            )

            # Process the authorized request
            response = self._process_request(request_type, payload, authorization)

            return {
                "success": True,
                "request_type": request_type,
                "authorization": authorization,
                "response": response,
            }

        except ProofGateError as e:
            return {
                "success": False,
                "request_type": request_type,
                "error": f"Authorization failed: {str(e)}",
                "provenance": provenance,
            }
        except Exception as e:
            return {
                "success": False,
                "request_type": request_type,
                "error": f"Processing error: {str(e)}",
                "provenance": provenance,
            }

    def _process_request(
        self, request_type: str, payload: dict[str, Any], authorization: dict[str, Any]
    ) -> dict[str, Any]:
        """
        Process the authorized request based on type
        """
        if request_type == "demo_action":
            return self._handle_demo_action(payload, authorization)
        elif request_type == "query":
            return self._handle_query(payload, authorization)
        elif request_type == "computation":
            return self._handle_computation(payload, authorization)
        else:
            return {
                "message": f"Processed {request_type} request",
                "payload": payload,
                "proof_token": authorization.get("proof_token"),
            }

    def _handle_demo_action(
        self, payload: dict[str, Any], authorization: dict[str, Any]
    ) -> dict[str, Any]:
        """Handle demo action request"""
        action_name = payload.get("action_name", "unknown")
        parameters = payload.get("parameters", {})

        return {
            "action_executed": True,
            "action_name": action_name,
            "parameters": parameters,
            "result": f"Demo action '{action_name}' executed successfully",
            "proof_token": authorization.get("proof_token"),
        }

    def _handle_query(
        self, payload: dict[str, Any], authorization: dict[str, Any]
    ) -> dict[str, Any]:
        """Handle query request"""
        query = payload.get("query", "")

        return {
            "query_processed": True,
            "query": query,
            "result": f"Query result for: {query}",
            "proof_token": authorization.get("proof_token"),
        }

    def _handle_computation(
        self, payload: dict[str, Any], authorization: dict[str, Any]
    ) -> dict[str, Any]:
        """Handle computation request"""
        computation_type = payload.get("type", "generic")
        inputs = payload.get("inputs", {})

        return {
            "computation_completed": True,
            "type": computation_type,
            "inputs": inputs,
            "result": f"Computation '{computation_type}' completed",
            "proof_token": authorization.get("proof_token"),
        }

    def health_check(self) -> dict[str, Any]:
        """Check health of LOGOS Nexus and underlying components"""
        validator_health = self.validator.reference_monitor.health_check()

        return {"nexus_status": "ok", "validator_health": validator_health}
