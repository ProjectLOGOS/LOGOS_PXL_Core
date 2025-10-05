"""
Privative Policies - Define obligations and invariant preservation requirements
Maps actions to their required proof obligations
"""

from typing import Dict, Any, List

class PrivativePolicies:
    def __init__(self):
        # Core policy mappings from actions to proof obligations
        self.action_policies = {
            "actuate": "Good(actuate) and TrueP(safe) and Coherent(state)",
            "plan": "Good(plan) and TrueP(feasible) and Coherent(context)",
            "compute": "Good(compute) and TrueP(deterministic) and Coherent(inputs)",
            "transform": "Good(transform) and TrueP(reversible) and Coherent(structure)",
            "communicate": "Good(communicate) and TrueP(authentic) and Coherent(message)",
            "persist": "Good(persist) and TrueP(integrity) and Coherent(data)",
            "query": "Good(query) and TrueP(authorized) and Coherent(scope)"
        }
        
        # Step-level invariant preservation requirements
        self.step_policies = {
            "init": "preserves_invariants(init) and maintains_consistency()",
            "process": "preserves_invariants(process) and maintains_coherence()",
            "finalize": "preserves_invariants(finalize) and ensures_completeness()",
            "analyze": "preserves_invariants(analyze) and maintains_objectivity()",
            "execute": "preserves_invariants(execute) and ensures_safety()",
            "validate": "preserves_invariants(validate) and maintains_rigor()",
            "optimize": "preserves_invariants(optimize) and maintains_correctness()"
        }
        
        # System-level coherence requirements
        self.system_policies = {
            "consistency": "consistency(semantics,axioms) and coherent_system(id)",
            "structure_preservation": "structure_preserved(op) and equivalent_structure(before,after)",
            "bijection_preservation": "preserves_good(name,x) and preserves_coherence(name)",
            "commutation": "commutes(g_name,h_name) and preserves_coherence_chain(g_name,h_name)"
        }
    
    def obligation_for(self, action: str, state: Dict[str, Any], properties: Dict[str, Any]) -> str:
        """
        Generate BOX obligation for a given action, state, and properties
        
        Args:
            action: The action being performed
            state: Current system state
            properties: Properties/parameters of the action
            
        Returns:
            String representation of the BOX obligation
        """
        # Get base obligation for the action type
        base_obligation = self.action_policies.get(action, f"Good({action}) and TrueP(valid) and Coherent(state)")
        
        # Enhance with specific properties if provided
        if properties:
            property_assertions = []
            for key, value in properties.items():
                if isinstance(value, bool):
                    if value:
                        property_assertions.append(f"TrueP({key})")
                    else:
                        property_assertions.append(f"not TrueP({key})")
                else:
                    # For non-boolean properties, assert they are valid/present
                    property_assertions.append(f"TrueP(valid_{key})")
            
            if property_assertions:
                enhanced_obligation = base_obligation + " and " + " and ".join(property_assertions)
                return enhanced_obligation
        
        return base_obligation
    
    def preserves_invariants(self, step: str) -> str:
        """
        Generate invariant preservation obligation for a plan step
        
        Args:
            step: The step identifier or type
            
        Returns:
            String representation of the preservation obligation
        """
        # Clean step identifier for use in logical formula
        step_clean = step.replace("-", "_").replace(" ", "_").lower()
        
        # Get specific preservation requirement or use generic
        specific_preservation = self.step_policies.get(step_clean, f"preserves_invariants({step_clean})")
        
        return specific_preservation
    
    def system_consistency_obligation(self, system_id: str, context: Dict[str, Any] = None) -> str:
        """
        Generate system-level consistency obligation
        
        Args:
            system_id: Identifier of the system
            context: Additional context for the consistency check
            
        Returns:
            String representation of the consistency obligation
        """
        base_obligation = f"consistency(semantics,axioms) and coherent_system({system_id})"
        
        if context:
            if context.get("drift_detected"):
                base_obligation += " and resolved_drift(semantics,axioms)"
            if context.get("rehabilitation"):
                base_obligation += f" and rehabilitated({system_id})"
        
        return base_obligation
    
    def bijection_preservation_obligation(self, bijection_name: str, operation_context: Dict[str, Any] = None) -> str:
        """
        Generate bijection preservation obligation
        
        Args:
            bijection_name: Name of the bijection
            operation_context: Context about the operation
            
        Returns:
            String representation of the preservation obligation
        """
        base_obligation = f"preserves_good({bijection_name},x) and preserves_coherence({bijection_name})"
        
        if operation_context:
            if operation_context.get("structural"):
                base_obligation += f" and preserves_structure({bijection_name})"
            if operation_context.get("reversible"):
                base_obligation += f" and is_bijection({bijection_name})"
        
        return base_obligation
    
    def commutation_obligation(self, g_name: str, h_name: str, commutativity_context: Dict[str, Any] = None) -> str:
        """
        Generate commutation obligation for composed operations
        
        Args:
            g_name: Name of first operation
            h_name: Name of second operation
            commutativity_context: Context about the commutation
            
        Returns:
            String representation of the commutation obligation
        """
        base_obligation = f"commutes({g_name},{h_name}) and preserves_coherence_chain({g_name},{h_name})"
        
        if commutativity_context:
            if commutativity_context.get("associative"):
                base_obligation += f" and associative({g_name},{h_name})"
            if commutativity_context.get("identity_preserving"):
                base_obligation += f" and preserves_identity({g_name},{h_name})"
        
        return base_obligation
    
    def get_all_policies(self) -> Dict[str, Dict[str, str]]:
        """Get all defined policies for inspection"""
        return {
            "action_policies": self.action_policies,
            "step_policies": self.step_policies,
            "system_policies": self.system_policies
        }