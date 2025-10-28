"""
hierarchical_bayes_network.py

Hierarchical Bayesian Network analysis.
"""
import json
import re
import numpy as np
from sklearn.linear_model import BayesianRidge
from sklearn.preprocessing import StandardScaler

def load_static_priors(path: str="config/bayes_priors.json") -> dict:
    with open(path) as f:
        return json.load(f)

def query_intent_analyzer(q: str) -> dict:
    flags=[]
    lw=q.lower()
    if any(w in lw for w in ['dragon','wizard','hogwarts']):
        flags.append("fictional")
    return {'is_valid': not flags, 'flags': flags, 'action':("reroute" if flags else "proceed")}

def preprocess_query(q: str) -> str:
    return re.sub(r'[^\\w\\s]','',q.lower())

def run_HBN_analysis(query: str, priors: dict) -> dict:
    cats=list(priors.keys())
    vals=np.array([priors.get(c,0) for c in cats]).reshape(-1,1)
    sc=StandardScaler().fit_transform(vals)
    mdl=BayesianRidge().fit(np.arange(len(cats)).reshape(-1,1), sc.ravel())
    idx=len(preprocess_query(query)) % len(cats)
    return {'prediction': mdl.predict([[idx]])[0], 'category': cats[idx]}

def execute_HBN(query: str) -> dict:
    p=load_static_priors()
    intent=query_intent_analyzer(query)
    if not intent['is_valid']:
        print("Flags:", intent['flags'])
        return {}
    return run_HBN_analysis(query,p)
