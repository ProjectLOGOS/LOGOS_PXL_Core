"""Bayesian Trinity Inferencer

Implements probabilistic inference for 3PDN dimensional mapping using Bayesian principles,
converting conceptual inputs to trinity vectors via theological priors. Constructs complex
parameters for fractal analysis and provides confidence metrics for predictions.

Core Capabilities:
- Prior-based inference for trinity vectors
- Weighted keyword processing
- Complex parameter generation for fractal analysis
- Trinitarian coherence preservation

Dependencies: typing, json, math
"""

from typing import Dict, List, Tuple, Optional, Union, Any
import json
import math

class BayesianTrinityInferencer:
    """Inferencer for trinitarian vectors using Bayesian prior probabilities."""
    
    def __init__(self, prior_path: str = "config/bayes_priors.json"):
        """Initialize inferencer with theological priors.
        
        Args:
            prior_path: Path to prior probabilities JSON file
        """
        self.priors = self._load_priors(prior_path)
    
    def _load_priors(self, path: str) -> Dict[str, Dict[str, float]]:
        """Load prior probabilities from file.
        
        Args:
            path: File path
            
        Returns:
            Prior probabilities dictionary
        """
        try:
            with open(path, 'r') as f:
                return json.load(f)
        except (IOError, json.JSONDecodeError) as e:
            # Default minimal priors on failure
            print(f"Warning: Failed to load priors from {path}: {e}")
            return {
                "existence": {"E": 0.7, "G": 0.5, "T": 0.6},
                "goodness": {"E": 0.6, "G": 0.9, "T": 0.7},
                "truth": {"E": 0.6, "G": 0.7, "T": 0.9}
            }
    
    def infer(self, 
             keywords: List[str], 
             weights: Optional[List[float]] = None) -> Dict[str, Any]:
        """Infer trinity vector and complex value from keywords.
        
        Args:
            keywords: List of key concepts to process
            weights: Optional weights for each keyword
            
        Returns:
            Dictionary with trinity vector, complex value, and source terms
            
        Raises:
            ValueError: If no keywords provided
        """
        if not keywords:
            raise ValueError("Must provide at least one keyword.")
        
        # Normalize keywords and validate weights
        norm_keywords = [k.lower() for k in keywords]
        if weights and len(weights) != len(norm_keywords):
            raise ValueError("Length of weights must match keywords.")
        
        # Use uniform weights if not provided
        weights = weights or [1.0] * len(norm_keywords)
        
        # Initialize dimension accumulators
        e_total, g_total, t_total = 0.0, 0.0, 0.0
        weight_sum = 0.0
        matched_terms = []
        
        # Process each keyword
        for i, term in enumerate(norm_keywords):
            entry = self.priors.get(term)
            if entry:
                # Apply weight to prior
                w = weights[i]
                e_total += entry["E"] * w
                g_total += entry["G"] * w
                t_total += entry["T"] * w
                weight_sum += w
                matched_terms.append(term)
        
        # Handle case with no matched priors
        if weight_sum == 0:
            raise ValueError("No valid priors found for given keywords.")
        
        # Calculate weighted averages
        e_avg = e_total / weight_sum
        g_avg = g_total / weight_sum
        t_avg = t_total / weight_sum
        
        # Ensure values in valid range [0,1]
        e = max(0.0, min(1.0, e_avg))
        g = max(0.0, min(1.0, g_avg))
        t = max(0.0, min(1.0, t_avg))
        
        # Create trinity vector
        trinity = (e, g, t)
        
        # Generate complex parameter for fractal analysis
        # c = complex(e * t, g) maps (existence * truth) → real component, goodness → imaginary
        c = complex(e * t, g)
        
        return {
            "trinity": trinity,
            "c": c,
            "source_terms": matched_terms
        }
    
    def infer_with_coherence(self, 
                           keywords: List[str], 
                           weights: Optional[List[float]] = None,
                           enforce_coherence: bool = True) -> Dict[str, Any]:
        """Infer trinity vector with coherence enforcement.
        
        Args:
            keywords: List of key concepts to process
            weights: Optional weights for each keyword
            enforce_coherence: Whether to enforce EGT coherence constraint
            
        Returns:
            Inference result with coherence metrics
        """
        # Get basic inference
        result = self.infer(keywords, weights)
        trinity = result["trinity"]
        
        # Extract trinity values
        e, g, t = trinity
        
        # Calculate coherence (E*T→G principle)
        ideal_g = e * t
        original_coherence = min(1.0, g / ideal_g) if ideal_g > 0 else 0.0
        
        # Enforce coherence if requested
        adjusted_trinity = trinity
        if enforce_coherence and g < ideal_g:
            # Adjust goodness to meet coherence requirement
            adjusted_g = ideal_g
            adjusted_trinity = (e, adjusted_g, t)
            
            # Update complex parameter
            result["c"] = complex(e * t, adjusted_g)
            result["trinity"] = adjusted_trinity
            result["coherence_adjusted"] = True
        
        # Add coherence metrics
        result["coherence"] = {
            "original": original_coherence,
            "ideal_goodness": ideal_g,
            "adjusted": enforce_coherence and g < ideal_g
        }
        
        return result
    
    def infer_trinity_path(self, 
                          keyword_sequence: List[List[str]], 
                          weights_sequence: Optional[List[List[float]]] = None) -> List[Dict[str, Any]]:
        """Infer sequence of trinity vectors from keyword progression.
        
        Args:
            keyword_sequence: List of keyword lists representing path
            weights_sequence: Optional sequence of weight lists
            
        Returns:
            List of inference results forming a path
        """
        path = []
        
        # Validate weights
        if weights_sequence and len(weights_sequence) != len(keyword_sequence):
            raise ValueError("Weights sequence must match keyword sequence length.")
        
        # Process each step in sequence
        for i, keywords in enumerate(keyword_sequence):
            weights = None
            if weights_sequence:
                weights = weights_sequence[i]
            
            # Infer with coherence
            result = self.infer_with_coherence(keywords, weights)
            
            # Add step information
            result["step"] = i
            path.append(result)
        
        return path
    
    def compute_trinity_distance(self, t1: Tuple[float, float, float], t2: Tuple[float, float, float]) -> float:
        """Compute Euclidean distance between trinity vectors.
        
        Args:
            t1: First trinity vector (e1, g1, t1)
            t2: Second trinity vector (e2, g2, t2)
            
        Returns:
            Distance metric in trinity space
        """
        return math.sqrt(
            (t1[0] - t2[0])**2 + 
            (t1[1] - t2[1])**2 + 
            (t1[2] - t2[2])**2
        )