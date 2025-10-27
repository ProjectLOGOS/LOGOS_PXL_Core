"""
bayesian_inferencer.py

Inferencer for trinitarian vectors via Bayesian priors.
"""
import json
from typing import Dict, List, Optional, Any, Tuple

class BayesianTrinityInferencer:
    def __init__(self, prior_path: str = "config/bayes_priors.json"):
        try:
            with open(prior_path) as f:
                self.priors: Dict[str,Dict[str,float]] = json.load(f)
        except:
            self.priors = {}

    def infer(self, keywords: List[str], weights: Optional[List[float]]=None) -> Dict[str,Any]:
        if not keywords:
            raise ValueError("Need ≥1 keyword")
        kws = [k.lower() for k in keywords]
        wts = weights if weights and len(weights)==len(kws) else [1.0]*len(kws)
        e_total=g_total=t_total=0.0
        sum_w=0.0
        matches=[]
        for i,k in enumerate(kws):
            entry = self.priors.get(k)
            if entry:
                w=wts[i]
                e_total+=entry.get("E",0)*w
                g_total+=entry.get("G",0)*w
                t_total+=entry.get("T",0)*w
                sum_w+=w
                matches.append(k)
        if sum_w==0:
            raise ValueError("No valid priors")
        e,g,t = e_total/sum_w, g_total/sum_w, t_total/sum_w
        e,g,t = max(0, min(1,e)), max(0,min(1,g)), max(0,min(1,t))
        c = complex(e*t, g)
        return {"trinity":(e,g,t), "c":c, "source_terms":matches}
