"""
Fractal Orbital Divergence Engine
Scaffold + operational code
"""
import math
import itertools
import logging
from typing import Tuple, List, Dict, Any, Optional

from ontological_node_class import OntologicalNode
from trinity_vector import TrinityVector

logger = logging.getLogger(__name__)

class DivergenceEngine:
    """
    Generates and evaluates alternative ontological states (variants)
    diverging from a base trinity vector.
    """
    def __init__(self, delta: float = 0.05, branches_to_return: int = 8):
        if not (0 < delta < 1):
            logger.warning(f"Delta {delta} out of range; resetting to 0.05")
            delta = 0.05
        self.delta = delta
        self.branches_to_return = max(1, branches_to_return)

    def generate_variants(self, base_vector: TrinityVector) -> List[TrinityVector]:
        e0, g0, t0 = base_vector.to_tuple()
        shifts = [-self.delta, 0.0, self.delta]
        variants = set()
        for de, dg, dt in itertools.product(shifts, repeat=3):
            if de==dg==dt==0: continue
            v = TrinityVector(e0+de, g0+dg, t0+dt)
            variants.add(v)
        logger.debug(f"Generated {len(variants)} variants")
        return list(variants)

    def evaluate_variant(self, variant_vector: TrinityVector) -> Dict[str, Any]:
        try:
            modal_info = variant_vector.calculate_modal_status()
            c_value = variant_vector.to_complex()
            node = OntologicalNode(c_value)
            orbit = node.orbit_properties
            return {
                "trinity_vector": variant_vector.to_tuple(),
                "c_value": (c_value.real, c_value.imag),
                "modal_status": modal_info[0],
                "confidence": modal_info[1],
                "coherence": modal_info[1],
                "fractal": {
                    "depth": orbit.get("depth", 0),
                    "in_set": orbit.get("in_set", False),
                    "lyapunov": orbit.get("lyapunov_exponent", 0.0)
                }
            }
        except Exception as e:
            logger.error(f"Error eval variant: {e}", exc_info=True)
            return {
                "error": str(e),
                "trinity_vector": variant_vector.to_tuple()
            }

    def analyze_divergence(self,
                           base_vector: TrinityVector,
                           sort_by: str = "coherence",
                           num_results: Optional[int] = None
                          ) -> List[Dict[str, Any]]:
        n = num_results or self.branches_to_return
        variants = self.generate_variants(base_vector)
        results = [self.evaluate_variant(v) for v in variants]
        results = [r for r in results if "error" not in r]
        keyfn = {
            "coherence": lambda x: x.get("coherence",0),
            "confidence": lambda x: x.get("confidence",0),
            "depth": lambda x: x["fractal"].get("depth",0),
        }.get(sort_by, lambda x: 0)
        results.sort(key=keyfn, reverse=True)
        return results[:n]
