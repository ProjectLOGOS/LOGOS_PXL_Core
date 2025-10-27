"""
mcmc_engine.py

MCMC Sampling via PyMC3.
"""
import pymc3 as pm
import numpy as np
import logging

logging.basicConfig(level=logging.INFO)
logger=logging.getLogger(__name__)

def run_mcmc_model(model_definition_func, draws=2000, tune=1000, chains=2, cores=1):
    with model_definition_func() as mdl:
        logger.info("Starting MCMC")
        trace = pm.sample(draws=draws, tune=tune, chains=chains, cores=cores, return_inferencedata=True)
        logger.info("MCMC complete")
    return trace

def example_model():
    model = pm.Model()
    with model:
        mu=pm.Normal('mu',0,1)
        obs=pm.Normal('obs',mu,1, observed=np.random.randn(100))
    return model
