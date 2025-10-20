from .scm import SCM
from typing import Dict

def evaluate_counterfactual(scm: SCM, target: str, context: Dict, intervention: Dict):
    """
    High-level API for evaluating a counterfactual query.
    P(target | do(intervention), context)
    """
    return scm.counterfactual({
        "target": target,
        "context": context,
        "do": intervention
    })