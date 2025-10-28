# fractal_nexus.py
"""
fractal_nexus.py

Toolkit-level Nexus orchestrator for Fractal Orbital Predictor.
"""
import traceback
import json

from class_fractal_orbital_predictor import TrinityPredictionEngine
from divergence_calculator import DivergenceEngine
from fractal_orbital_node_generator import FractalNodeGenerator
from orbital_recursion_engine import OntologicalSpace

class FractalNexus:
    def __init__(self, prior_path: str):
        self.predictor = TrinityPredictionEngine(prior_path)
        self.divergence = DivergenceEngine()
        self.generator = FractalNodeGenerator()
        self.mapper    = OntologicalSpace()

    def run_predict(self, keywords: List[str]) -> Dict:
        try:
            res = self.predictor.predict(keywords)
            return {'output': res, 'error': None}
        except Exception:
            return {'output': None, 'error': traceback.format_exc()}

    def run_divergence(self, trinity_vector: Tuple[float, float, float]) -> Dict:
        try:
            variants = self.divergence.analyze_divergence(trinity_vector)
            return {'output': variants, 'error': None}
        except Exception:
            return {'output': None, 'error': traceback.format_exc()}

    def run_generate(self, c_value: complex) -> Dict:
        try:
            nodes = self.generator.generate(c_value)
            return {'output': nodes, 'error': None}
        except Exception:
            return {'output': None, 'error': traceback.format_exc()}

    def run_map(self, query_vector: Tuple[float, float, float]) -> Dict:
        try:
            pos = self.mapper.compute_fractal_position(query_vector)
            return {'output': pos, 'error': None}
        except Exception:
            return {'output': None, 'error': traceback.format_exc()}

    def run_pipeline(self, keywords: List[str]) -> List[Dict]:
        report = []
        # 1) Predict
        p = self.run_predict(keywords)
        report.append({'step': 'predict', **p})
        if p['error'] or not p['output']:
            return report

        # Extract trinity & c_value
        trinity = p['output'].get('trinity')
        c_val   = p['output'].get('c_value')

        # 2) Divergence on trinity
        d = self.run_divergence(trinity)
        report.append({'step': 'divergence', **d})

        # 3) Generate nodes from c_value
        try:
            # convert c_value string to complex if needed
            c = complex(c_val) if isinstance(c_val, str) else c_val
        except:
            c = c_val
        g = self.run_generate(c)
        report.append({'step': 'generate', **g})

        # 4) Map trinity -> position (using first variant if available)
        if d['output']:
            first_tv = d['output'][0].get('trinity_vector')
            m = self.run_map(first_tv)
            report.append({'step': 'map', **m})

        return report

if __name__ == '__main__':
    import sys, pprint

    if len(sys.argv) < 3:
        print("Usage: python fractal_nexus.py <prior_path> <keyword1> [keyword2 ...]")
        sys.exit(1)

    prior = sys.argv[1]
    keywords = sys.argv[2:]
    nexus = FractalNexus(prior)
    result = nexus.run_pipeline(keywords)
    pprint.pprint(result)
    with open('fractal_nexus_report.json', 'w') as f:
        json.dump(result, f, indent=2)
