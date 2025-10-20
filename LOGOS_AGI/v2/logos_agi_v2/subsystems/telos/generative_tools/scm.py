from collections import defaultdict
try:
    from causallearn.search.ConstraintBased.PC import pc
    from causallearn.utils.cit import fisherz
    CAUSALLEARN_AVAILABLE = True
except ImportError:
    CAUSALLEARN_AVAILABLE = False
    pc = None
    fisherz = None
	
class SCM:
    """
    Structural Causal Model with async fit capability.
    """
    def __init__(self, dag=None):
        self.dag = dag or {}
        self.parameters = {}

    def fit(self, data: list):
        """
        Fits the structural equations to the data.
        In a full implementation, this would use a causal discovery algorithm.
        For now, it calculates conditional probabilities based on the given DAG.
        """
        from causallearn.search.ConstraintBased.PC import pc
        from causallearn.utils.cit import fisherz
        import pandas as pd

        if len(data) > 50 and not self.dag:
            print("[SCM] Performing causal discovery...")
            df = pd.DataFrame(data)
            df = df.apply(pd.to_numeric, errors='coerce').dropna()
            if not df.empty:
                cg = pc(df.to_numpy(), alpha=0.05, ci_test=fisherz, verbose=False)
                # This learned graph could be used to update self.dag
        
        counts = {}
        for node, parents in self.dag.items():
            counts[node] = defaultdict(lambda: defaultdict(int))
            for sample in data:
                if all(p in sample for p in parents):
                    key = tuple(sample.get(p) for p in parents) if parents else ()
                    val = sample.get(node)
                    if val is not None:
                        counts[node][key][val] += 1
            
            self.parameters[node] = {
                key: {v: c / sum(freq.values()) for v, c in freq.items()}
                for key, freq in counts[node].items() if sum(freq.values()) > 0
            }
        return True

    def do(self, intervention: dict):
        new = SCM(dag=self.dag)
        new.parameters = self.parameters.copy()
        new.intervention = intervention
        return new

    def counterfactual(self, query: dict):
        target = query.get('target')
        do = query.get('do', {})
        
        if target in do:
            return 1.0
            
        params = self.parameters.get(target, {})
        if not params:
            return 0.0
            
        total_prob = sum(sum(dist.values()) for dist in params.values())
        num_outcomes = sum(len(dist) for dist in params.values())
        return total_prob / num_outcomes if num_outcomes > 0 else 0.0