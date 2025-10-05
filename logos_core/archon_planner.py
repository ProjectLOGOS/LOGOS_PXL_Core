"""
Archon Planner - Proof-gated planning with step-by-step validation
All planner edges require proof tokens
"""

import sys
import os
from typing import List, Dict, Any

# Add parent directory to path for imports
sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from logos_core.unified_formalisms import UnifiedFormalismValidator
from logos_core.reference_monitor import ProofGateError

class ArchonPlannerGate:
    def __init__(self, config_path: str = None):
        if config_path is None:
            # Default to config in parent directory
            current_dir = os.path.dirname(os.path.abspath(__file__))
            config_path = os.path.join(os.path.dirname(current_dir), "configs", "config.json")
        self.validator = UnifiedFormalismValidator(config_path)
    
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