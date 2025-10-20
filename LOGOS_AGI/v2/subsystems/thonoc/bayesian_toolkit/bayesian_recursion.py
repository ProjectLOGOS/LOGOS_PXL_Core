"""
bayesian_recursion.py

Recursive Bayesian belief updater.
"""
import pickle
from pathlib import Path
from dataclasses import dataclass
from typing import Dict, List
from datetime import datetime
import numpy as np
from scipy import stats

@dataclass
class BayesianPrediction:
    prediction: float
    confidence: float
    variance: float
    timestamp: str
    metadata: Dict

@dataclass
class ModelState:
    priors: Dict[str,float]
    likelihoods: Dict[str,float]
    posterior_history: List[Dict[str,float]]
    variance_metrics: Dict[str,float]
    performance_metrics: Dict[str,float]

class BayesianMLModel:
    def __init__(self, data_path: str="data/bayesian_model_data.pkl"):
        self.path = Path(data_path)
        self._load_or_init()

    def _load_or_init(self):
        if self.path.exists():
            try:
                with open(self.path,'rb') as f:
                    self.state: ModelState = pickle.load(f)
            except:
                self._init_state()
        else:
            self._init_state()

    def _init_state(self):
        self.state = ModelState({'default':0.5}, {}, [], {'global_variance':0.0}, {'accuracy':0.0,'confidence':0.0})
        with open(self.path,'wb') as f:
            pickle.dump(self.state,f)

    def update_belief(self, hypothesis: str, evidence: Dict[str,float]) -> BayesianPrediction:
        prior = self.state.priors.get(hypothesis,0.5)
        lik = self._likelihood(hypothesis, evidence)
        marg = self._marginal(evidence)
        post = (prior * lik)/marg if marg else prior
        conf = (post * np.mean(list(evidence.values())) * np.mean(list(self.state.priors.values())))**(1/3)
        vars_ = np.var([p['prediction'] for p in self.state.posterior_history[-10:]]+[post]) if self.state.posterior_history else 0.0
        pred = BayesianPrediction(post,conf,vars_,datetime.now().isoformat(), {'evidence':evidence,'prior':prior})
        self.state.posterior_history.append({'prediction':pred.prediction,'confidence':pred.confidence,'variance':pred.variance,'timestamp':pred.timestamp})
        with open(self.path,'wb') as f:
            pickle.dump(self.state,f)
        return pred

    def _likelihood(self, hypothesis,evidence):
        return np.prod([stats.norm.pdf(val, loc=self.state.likelihoods.get(f"{hypothesis}|{k}",0), scale=0.1)
                        for k,val in evidence.items()]) or 0.5

    def _marginal(self, evidence):
        return sum(self.state.priors[h]*self.update_belief(h,evidence).prediction 
                   for h in self.state.priors)
