"""
PXL Client - HTTP client for communicating with PXL proof server
"""

import requests
import json
from typing import Dict, Any, Optional

class PXLClient:
    def __init__(self, prover_url: str, timeout_ms: int = 2000):
        self.prover_url = prover_url
        self.timeout_sec = timeout_ms / 1000.0
    
    def prove_box(self, goal: str) -> Dict[str, Any]:
        """
        Request proof of a BOX obligation from PXL server
        Returns: {ok: bool, id: str, kernel_hash: str, goal: str, ...}
        """
        try:
            response = requests.post(
                f"{self.prover_url}/prove",
                json={"goal": goal},
                timeout=self.timeout_sec
            )
            response.raise_for_status()
            return response.json()
        except requests.exceptions.Timeout:
            return {
                "ok": False,
                "error": "Proof request timed out",
                "goal": goal
            }
        except requests.exceptions.RequestException as e:
            return {
                "ok": False,
                "error": f"Network error: {str(e)}",
                "goal": goal
            }
        except json.JSONDecodeError:
            return {
                "ok": False,
                "error": "Invalid JSON response from prover",
                "goal": goal
            }
    
    def countermodel(self, goal: str) -> Dict[str, Any]:
        """
        Request countermodel for a goal from PXL server
        Returns: {countermodel_found: bool, kernel_hash: str, goal: str, ...}
        """
        try:
            response = requests.post(
                f"{self.prover_url}/countermodel",
                json={"goal": goal},
                timeout=self.timeout_sec
            )
            response.raise_for_status()
            return response.json()
        except requests.exceptions.Timeout:
            return {
                "countermodel_found": False,
                "error": "Countermodel request timed out",
                "goal": goal
            }
        except requests.exceptions.RequestException as e:
            return {
                "countermodel_found": False,
                "error": f"Network error: {str(e)}",
                "goal": goal
            }
        except json.JSONDecodeError:
            return {
                "countermodel_found": False,
                "error": "Invalid JSON response from prover",
                "goal": goal
            }
    
    def health_check(self) -> Dict[str, Any]:
        """Check if PXL server is healthy and get kernel hash"""
        try:
            response = requests.get(
                f"{self.prover_url}/health",
                timeout=self.timeout_sec
            )
            response.raise_for_status()
            return response.json()
        except Exception as e:
            return {
                "status": "error",
                "error": str(e)
            }