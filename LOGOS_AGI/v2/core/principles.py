# principles.py

import math
from typing import Dict

def sign_principle(metrics: Dict[str, float]) -> float:
    """
    SIGN principle value in [0,1]:
    geometric mean of connectivity, sync, covariance.
    """
    c = metrics.get('connectivity_score', 0.0)
    s = metrics.get('sync_score', 0.0)
    v = metrics.get('covariance_score', 0.0)
    eps = 1e-6
    return ((c+eps)*(s+eps)*(v+eps))**(1/3)

def bridge_principle(p_x: float) -> float:
    """
    BRIDGE principle value: 1 - P(x), clipped to [0,1].
    """
    return max(0.0, 1.0 - p_x)

def mind_principle(metrics: Dict[str, float]) -> float:
    """
    MIND principle stub: use sync_score as proxy.
    """
    return metrics.get('sync_score', 0.0)

def non_contradiction_principle(metrics: Dict[str, float]) -> float:
    """
    Non-contradiction stub: 1 - contradiction_score.
    """
    return max(0.0, 1.0 - metrics.get('contradiction_score', 0.0))
