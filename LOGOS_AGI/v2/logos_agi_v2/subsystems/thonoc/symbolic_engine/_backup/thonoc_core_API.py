"""
thonoc_core_API.py

Public API layer for THŌNOC core functionality.
"""
import json, math
from typing import Dict, List, Tuple, Optional, Any

from ontology.trinity_vector import TrinityVector
from thonoc_core import ThonocCore
from thonoc_fractal_mapping import FractalNavigator
from modal_inference import ThonocModalInference as ModalInferenceEngine

class ThonocCoreAPI:
    """High-level interface to THŌNOC system."""
    def __init__(self, config_path: Optional[str]=None):
        self.core = ThonocCore(config_path)

    def run(self, query: str) -> Dict[str, Any]:
        """
        Single-call entry point: returns full pipeline result.
        """
        return self.core.process_query(query)

    def get_coherence(self, tv: Tuple[float,float,float]) -> float:
        """
        Compute coherence of a TrinityVector.
        """
        e,g,t = tv
        ideal = e*t
        return 1.0 if g>=ideal else (g/ideal if ideal>0 else 0.0)

    def find_entailments(self, node_id: str, depth: int=1) -> List[Dict[str,Any]]:
        """Stub: expose entailments from knowledge store (if implemented)."""
        return []
