"""
OBDC Kernel - Structure-preserving mappings with proof gates
All bijections and commutative operations require proof tokens
"""

import sys
import os
from typing import Dict, Any, Callable

# Add parent directory to path for imports
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from logos_core.reference_monitor import ReferenceMonitor, ProofGateError

class OBDCKernel:
    def __init__(self, config_path: str = None):
        if config_path is None:
            # Default to config in parent directory
            current_dir = os.path.dirname(os.path.abspath(__file__))
            config_path = os.path.join(os.path.dirname(current_dir), "configs", "config.json")
        self.reference_monitor = ReferenceMonitor(config_path)
        self.registered_bijections = {}
        self.registered_commutations = {}
    
    def apply_bijection(self, name: str, f: Callable, x: Any, provenance: Dict[str, Any]) -> Any:
        """
        Apply a bijection with proof that it preserves Good and Coherence
        
        Args:
            name: Name/identifier of the bijection
            f: The bijection function to apply
            x: Input value
            provenance: Context about the application
            
        Returns:
            Result of f(x)
            
        Raises:
            ProofGateError: If proof requirements are not met
        """
        # Require proof that bijection preserves Good and Coherence
        obligation = f"BOX(preserves_good({name},x) and preserves_coherence({name}))"
        
        proof_token = self.reference_monitor.require_proof_token(obligation, provenance)
        
        # Apply the bijection
        try:
            result = f(x)
            
            # Register successful application
            self.registered_bijections[name] = {
                "function": f.__name__ if hasattr(f, '__name__') else str(f),
                "input": str(x)[:100],  # Truncate for logging
                "output": str(result)[:100],
                "proof_token": proof_token,
                "provenance": provenance
            }
            
            return result
            
        except Exception as e:
            raise ProofGateError(f"Bijection {name} failed during application: {str(e)}")
    
    def commute(self, g_name: str, h_name: str, g: Callable, h: Callable, s: Any, provenance: Dict[str, Any]) -> Any:
        """
        Apply commuting operations g∘h with proof of commutativity and coherence preservation
        
        Args:
            g_name: Name of first operation
            h_name: Name of second operation  
            g: First operation function
            h: Second operation function
            s: Input state/value
            provenance: Context about the commutation
            
        Returns:
            Result of g(h(s))
            
        Raises:
            ProofGateError: If proof requirements are not met
        """
        # Require proof of commutativity and coherence preservation
        obligation = f"BOX(commutes({g_name},{h_name}) and preserves_coherence_chain({g_name},{h_name}))"
        
        proof_token = self.reference_monitor.require_proof_token(obligation, provenance)
        
        # Apply the commuting operations
        try:
            intermediate = h(s)
            result = g(intermediate)
            
            # Register successful commutation
            commute_key = f"{g_name}∘{h_name}"
            self.registered_commutations[commute_key] = {
                "g_name": g_name,
                "h_name": h_name,
                "input": str(s)[:100],
                "intermediate": str(intermediate)[:100],
                "output": str(result)[:100],
                "proof_token": proof_token,
                "provenance": provenance
            }
            
            return result
            
        except Exception as e:
            raise ProofGateError(f"Commutation {g_name}∘{h_name} failed during application: {str(e)}")
    
    def register_verified_bijection(self, name: str, f: Callable, provenance: Dict[str, Any]) -> Dict[str, Any]:
        """
        Pre-register a bijection with upfront verification
        """
        try:
            # Require proof that this is indeed a bijection that preserves properties
            obligation = f"BOX(is_bijection({name}) and preserves_good({name}) and preserves_coherence({name}))"
            proof_token = self.reference_monitor.require_proof_token(obligation, provenance)
            
            self.registered_bijections[name] = {
                "function": f.__name__ if hasattr(f, '__name__') else str(f),
                "pre_verified": True,
                "proof_token": proof_token,
                "provenance": provenance
            }
            
            return {
                "registered": True,
                "name": name,
                "proof_token": proof_token
            }
            
        except ProofGateError as e:
            return {
                "registered": False,
                "name": name,
                "error": str(e)
            }
    
    def verify_structure_preservation(self, operation_name: str, before_state: Any, after_state: Any, provenance: Dict[str, Any]) -> Dict[str, Any]:
        """
        Verify that an operation preserved required structures
        """
        try:
            # Require proof that structure was preserved
            obligation = f"BOX(structure_preserved({operation_name}) and equivalent_structure(before,after))"
            proof_token = self.reference_monitor.require_proof_token(obligation, provenance)
            
            return {
                "structure_preserved": True,
                "operation": operation_name,
                "proof_token": proof_token
            }
            
        except ProofGateError as e:
            return {
                "structure_preserved": False,
                "operation": operation_name,
                "error": str(e)
            }
    
    def get_kernel_status(self) -> Dict[str, Any]:
        """Get current status of OBDC kernel"""
        return {
            "registered_bijections": len(self.registered_bijections),
            "registered_commutations": len(self.registered_commutations),
            "bijection_names": list(self.registered_bijections.keys()),
            "commutation_names": list(self.registered_commutations.keys())
        }