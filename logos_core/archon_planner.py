"""
Archon Planner Gate - Per-edge preservation + plan reachability + countermodel pruning
All planner edges require proof tokens with comprehensive validation
"""

import sys
import os
from typing import List, Dict, Any

# Add parent directory to path for imports
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from policies.privative_policies import preserves_invariants
from logos_core.unified_formalisms import UnifiedFormalismValidator
from logos_core.reference_monitor import ReferenceMonitor, ProofGateError

class ArchonPlannerGate:
    def __init__(self, config_path: str = None):
        if config_path is None:
            # Default to config in parent directory
            current_dir = os.path.dirname(os.path.abspath(__file__))
            config_path = os.path.join(os.path.dirname(current_dir), "configs", "config.json")
        
        self.validator = UnifiedFormalismValidator(config_path)
        self.rm = ReferenceMonitor(config_path)
        self.client = self.rm.pxl_client
        self.verified_plans = {}
        self.verified_steps = {}
    
    def create_plan(self, goal: str, context: Dict[str, Any], provenance: Dict[str, Any]) -> Dict[str, Any]:
        """
        Create a plan with proof-gated validation
        
        Args:
            goal: The goal to achieve
            context: Planning context and constraints
            provenance: Information about who requested the plan
            
        Returns:
            Dict with plan details and proof tokens
        """
        plan_id = f"plan_{hash(goal + str(context)) % 10000}"
        
        # First validate the plan-level goal
        plan_validation = self.validator.validate_plan_goal(plan_id, goal, provenance)
        
        # Generate plan steps (simplified for demo)
        steps = self._generate_steps(goal, context)
        
        # Validate each step requires BOX(preserves_invariants(step))
        validated_steps = []
        for step in steps:
            try:
                step_validation = self.validator.validate_plan_step(step, provenance)
                validated_steps.append({
                    **step,
                    "validation": step_validation
                })
            except ProofGateError as e:
                # Step failed validation - reject entire plan
                return {
                    "plan_created": False,
                    "plan_id": plan_id,
                    "error": f"Step {step.get('id')} failed validation: {str(e)}",
                    "failed_step": step
                }
        
        return {
            "plan_created": True,
            "plan_id": plan_id,
            "goal": goal,
            "steps": validated_steps,
            "plan_validation": plan_validation
        }
    
    def check_step(self, step: str, provenance: Dict[str, Any]) -> Dict[str, Any]:
        """Check that a workflow step preserves invariants"""
        obligation = f"BOX({preserves_invariants(step)})"
        proof_token = self.rm.require_proof_token(obligation, dict(provenance, step=step))
        
        # Cache verified step
        self.verified_steps[step] = {
            "obligation": obligation,
            "proof_token": proof_token,
            "provenance": provenance
        }
        
        return proof_token

    def check_plan_reachability(self, plan_id: str) -> None:
        """Verify plan reachability using DIAMOND modality"""
        reachability_goal = f"DIAMOND(Goal({plan_id}))"
        
        # Use PXL client directly for DIAMOND checking
        result = self.client.prove_box(reachability_goal)
        
        if not result.get("ok", False):
            raise ValueError(f"plan not reachable (¬◇Goal): {result.get('error', 'Unknown error')}")

    def prune_on_countermodel(self, safety_phi: str) -> None:
        """Prune plan if countermodel found for safety property"""
        countermodel_result = self.client.countermodel(safety_phi)
        
        if countermodel_result.get("countermodel_found", False):
            raise ValueError(f"countermodel found; plan unsafe: {countermodel_result.get('countermodel_desc', 'No description')}")

    def authorize_plan(self, steps: List[str], plan_id: str, provenance: Dict[str, Any]) -> bool:
        """
        Comprehensive plan authorization with:
        - Per-step invariant preservation
        - Plan reachability verification  
        - Safety countermodel pruning
        """
        try:
            # Check each step preserves invariants
            for step in steps:
                self.check_step(step, dict(provenance, plan_id=plan_id, step=step))
            
            # Verify plan is reachable
            self.check_plan_reachability(plan_id)
            
            # Prune if countermodel exists for safety
            safety_property = f"no_harm_trace({plan_id})"
            self.prune_on_countermodel(safety_property)
            
            # Cache successful plan authorization
            self.verified_plans[plan_id] = {
                "steps": steps,
                "all_steps_verified": True,
                "reachability_verified": True,
                "safety_verified": True,
                "provenance": provenance
            }
            
            return True
            
        except (ProofGateError, ValueError) as e:
            # Log failed plan
            self.verified_plans[plan_id] = {
                "steps": steps,
                "authorization_failed": True,
                "error": str(e),
                "provenance": provenance
            }
            raise
    
    def execute_step(self, plan_id: str, step_id: str, step_data: Dict[str, Any], provenance: Dict[str, Any]) -> Dict[str, Any]:
        """
        Execute a single plan step with proof gate
        
        Args:
            plan_id: ID of the plan
            step_id: ID of the step within the plan
            step_data: Data/parameters for the step
            provenance: Execution context
            
        Returns:
            Dict with execution result
        """
        # Each step execution requires fresh proof
        step = {"id": step_id, **step_data}
        
        try:
            validation = self.validator.validate_plan_step(step, provenance)
            
            # Simulate step execution (real implementation would call actual tools/actions)
            execution_result = self._execute_step_impl(step)
            
            return {
                "step_executed": True,
                "plan_id": plan_id,
                "step_id": step_id,
                "validation": validation,
                "result": execution_result
            }
            
        except ProofGateError as e:
            return {
                "step_executed": False,
                "plan_id": plan_id,
                "step_id": step_id,
                "error": str(e)
            }
    
    def _generate_steps(self, goal: str, context: Dict[str, Any]) -> List[Dict[str, Any]]:
        """
        Generate plan steps for the given goal (simplified implementation)
        """
        # Simple step generation for demo
        if "demo" in goal.lower():
            return [
                {"id": "init", "action": "initialize", "params": {"goal": goal}},
                {"id": "process", "action": "process", "params": {"context": context}},
                {"id": "finalize", "action": "finalize", "params": {"goal": goal}}
            ]
        else:
            return [
                {"id": "analyze", "action": "analyze_goal", "params": {"goal": goal}},
                {"id": "execute", "action": "execute_goal", "params": {"goal": goal, "context": context}}
            ]
    
    def _execute_step_impl(self, step: Dict[str, Any]) -> Dict[str, Any]:
        """
        Actual step execution implementation (simplified for demo)
        """
        action = step.get("action", "unknown")
        params = step.get("params", {})
        
        # Simulate different action types
        if action == "initialize":
            return {"status": "initialized", "message": f"Initialized for goal: {params.get('goal')}"}
        elif action == "process":
            return {"status": "processed", "message": "Processing completed"}
        elif action == "finalize":
            return {"status": "finalized", "message": "Goal finalized"}
        elif action == "analyze_goal":
            return {"status": "analyzed", "analysis": f"Goal analysis: {params.get('goal')}"}
        elif action == "execute_goal":
            return {"status": "executed", "message": f"Executed goal: {params.get('goal')}"}
        else:
            return {"status": "completed", "message": f"Completed action: {action}"}