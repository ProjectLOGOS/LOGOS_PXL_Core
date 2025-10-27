# bayesian_nexus.py
"""
bayesian_nexus.py

Toolkit-level Nexus orchestrator for Bayesian Predictor.
"""
import traceback
import json

from bayes_update_real_time import run_BERT_pipeline
from bayesian_inferencer import BayesianTrinityInferencer
from hierarchical_bayes_network import execute_HBN
from bayesian_recursion import BayesianMLModel
from mcmc_engine import run_mcmc_model, example_model

class BayesianNexus:
    def __init__(self, priors_path: str):
        self.priors_path = priors_path
        self.inferencer = BayesianTrinityInferencer(prior_path=priors_path)
        self.recursion_model = BayesianMLModel()

    def run_real_time(self, query: str) -> Dict:
        try:
            ok, log = run_BERT_pipeline(self.priors_path, query)
            return {'output': {'success': ok, 'log': log}, 'error': None}
        except Exception:
            return {'output': None, 'error': traceback.format_exc()}

    def run_inferencer(self, query: str) -> Dict:
        try:
            res = self.inferencer.infer(query.split())
            return {'output': res, 'error': None}
        except Exception:
            return {'output': None, 'error': traceback.format_exc()}

    def run_hbn(self, query: str) -> Dict:
        try:
            res = execute_HBN(query)
            # ensure only numeric prediction
            pred = float(res.get('prediction', 0.0))
            return {'output': {'prediction': pred}, 'error': None}
        except Exception:
            return {'output': None, 'error': traceback.format_exc()}

    def run_recursion(self, evidence: Dict) -> Dict:
        try:
            pred = self.recursion_model.update_belief('hypothesis', evidence)
            return {'output': {'prediction': pred.prediction}, 'error': None}
        except Exception:
            return {'output': None, 'error': traceback.format_exc()}

    def run_mcmc(self) -> Dict:
        try:
            trace = run_mcmc_model(example_model)
            return {'output': {'n_samples': len(getattr(trace, 'posterior', []))}, 'error': None}
        except Exception:
            return {'output': None, 'error': traceback.format_exc()}

    def run_pipeline(self, query: str) -> List[Dict]:
        report = []
        # Stage 1: Real-Time
        r1 = self.run_real_time(query)
        report.append({'stage': 'real_time', **r1})

        # Stage 2: Inferencer
        r2 = self.run_inferencer(query)
        report.append({'stage': 'inferencer', **r2})

        # Stage 3: HBN
        r3 = self.run_hbn(query)
        report.append({'stage': 'hbn', **r3})

        # Stage 4: Recursion (uses trinity from inferencer)
        evidence = r2['output'] if r2['output'] else {}
        r4 = self.run_recursion(evidence)
        report.append({'stage': 'recursion', **r4})

        # Stage 5: MCMC
        r5 = self.run_mcmc()
        report.append({'stage': 'mcmc', **r5})

        return report

if __name__ == '__main__':
    import sys
    import pprint

    if len(sys.argv) < 2:
        print("Usage: python bayesian_nexus.py '<query>'")
        sys.exit(1)

    query = sys.argv[1]
    nexus = BayesianNexus(priors_path='config/bayes_priors.json')
    result = nexus.run_pipeline(query)
    pprint.pprint(result)
    # Optionally write to JSON
    with open('bayesian_nexus_report.json', 'w') as f:
        json.dump(result, f, indent=2)
