from .scm import SCM

class Planner:
    """
    A simple planner that generates a sequence of interventions to reach a goal state.
    """
    def __init__(self, scm: SCM, max_depth: int = 5):
        self.scm = scm
        self.max_depth = max_depth

    def plan(self, goal: dict):
        plan = []
        current_state_scm = self.scm

        for var, target_val in goal.items():
            intervention = {var: target_val}
            
            prob = current_state_scm.do(intervention).counterfactual({
                'target': var,
                'do': intervention,
                'context': {}
            })

            if prob >= 0.5:
                plan.append({"action": "intervene", "details": intervention, "confidence": prob})
                current_state_scm = current_state_scm.do(intervention)
            else:
                plan.append({"action": "note", "details": f"Intervention {intervention} is unlikely to succeed.", "confidence": prob})
        
        return plan