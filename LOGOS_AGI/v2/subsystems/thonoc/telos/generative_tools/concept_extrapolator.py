# extrapolator.py

import random
from typing import Any, Dict, List

class Extrapolator:
    """
    Lightweight synthetic node generator:
    samples existing nodes, recombines payload text.
    """
    def __init__(self, generator):
        self.generator = generator

    def sample_nodes(self, k: int) -> List[Dict[str, Any]]:
        """Randomly sample up to k existing nodes."""
        nodes = self.generator.nodes
        return random.sample(nodes, min(k, len(nodes))) if nodes else []

    def generate_synthetic_payload(self, samples: List[Dict[str, Any]]) -> Any:
        """Combine text from sampled node payloads to form a new payload."""
        words = []
        for node in samples:
            payload = node.get('payload')
            if isinstance(payload, str):
                words.extend(payload.split())
        random.shuffle(words)
        # Take first 10 words or all
        text = ' '.join(words[:10])
        return {'text': text or 'synthetic_node'}
