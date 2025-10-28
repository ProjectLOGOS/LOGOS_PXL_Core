"""
Epistemological Framework

Provides frameworks for epistemological analysis, justification theories,
and knowledge validation methodologies.
"""

from typing import Dict, List, Any, Optional, Set, Callable
from enum import Enum
from dataclasses import dataclass

class EpistemologyType(Enum):
    RATIONALISM = "rationalism"
    EMPIRICISM = "empiricism"
    CONSTRUCTIVISM = "constructivism"
    PRAGMATISM = "pragmatism"
    COHERENTISM = "coherentism"
    FOUNDATIONALISM = "foundationalism"

class JustificationCriterion(Enum):
    TRUTH = "truth"
    WARRANT = "warrant"
    RELIABILITY = "reliability"
    COHERENCE = "coherence"
    UTILITY = "utility"

@dataclass
class Belief:
    """Represents a belief with epistemological properties."""
    proposition: str
    confidence: float
    justification_chain: List[str]
    supporting_evidence: List[Any]
    counter_evidence: List[Any]
    last_updated: float

@dataclass
class JustificationTheory:
    """Represents a theory of epistemic justification."""
    name: str
    criteria: List[JustificationCriterion]
    validation_function: Callable
    strength_assessment: Callable

class EpistemologicalFramework:
    """
    Framework for epistemological analysis and justification.

    Supports multiple epistemological theories, belief systems,
    and justification methodologies.
    """

    def __init__(self, primary_theory: EpistemologyType = EpistemologyType.COHERENTISM):
        self.primary_theory = primary_theory
        self.beliefs: Dict[str, Belief] = {}
        self.justification_theories: Dict[str, JustificationTheory] = {}
        self.epistemic_virtues: Set[str] = {
            "intellectual_humility", "curiosity", "open_mindedness",
            "intellectual_courage", "intellectual_autonomy"
        }

        self._initialize_default_theories()

    def _initialize_default_theories(self):
        """Initialize default epistemological theories."""
        self.add_justification_theory(JustificationTheory(
            name="coherentist",
            criteria=[JustificationCriterion.COHERENCE, JustificationCriterion.WARRANT],
            validation_function=self._validate_coherence,
            strength_assessment=self._assess_coherence_strength
        ))

        self.add_justification_theory(JustificationTheory(
            name="foundationalist",
            criteria=[JustificationCriterion.TRUTH, JustificationCriterion.WARRANT],
            validation_function=self._validate_foundational,
            strength_assessment=self._assess_foundational_strength
        ))

        self.add_justification_theory(JustificationTheory(
            name="reliabilist",
            criteria=[JustificationCriterion.RELIABILITY, JustificationCriterion.WARRANT],
            validation_function=self._validate_reliability,
            strength_assessment=self._assess_reliability_strength
        ))

    def add_justification_theory(self, theory: JustificationTheory):
        """Add a justification theory."""
        self.justification_theories[theory.name] = theory

    def add_belief(self, belief: Belief):
        """Add a belief to the framework."""
        belief_id = hash(belief.proposition) % 1000000  # Simple ID generation
        self.beliefs[str(belief_id)] = belief

    def justify_belief(self, belief_id: str, theory_name: str = None) -> Dict[str, Any]:
        """Justify a belief using specified theory."""
        if belief_id not in self.beliefs:
            return {"justified": False, "reason": "Belief not found"}

        belief = self.beliefs[belief_id]
        theory = self.justification_theories.get(theory_name or self.primary_theory.value)

        if not theory:
            return {"justified": False, "reason": "Justification theory not found"}

        try:
            validation_result = theory.validation_function(belief)
            strength = theory.strength_assessment(belief)

            return {
                "justified": validation_result,
                "strength": strength,
                "theory_used": theory.name,
                "criteria_satisfied": theory.criteria
            }
        except Exception as e:
            return {"justified": False, "reason": str(e)}

    def _validate_coherence(self, belief: Belief) -> bool:
        """Validate belief using coherentist criteria."""
        # Check if belief coheres with existing beliefs
        coherence_score = 0.0

        for other_belief in self.beliefs.values():
            if other_belief != belief:
                # Simplified coherence check
                if self._beliefs_coherent(belief, other_belief):
                    coherence_score += 1.0

        return coherence_score / max(1, len(self.beliefs) - 1) > 0.5

    def _validate_foundational(self, belief: Belief) -> bool:
        """Validate belief using foundationalist criteria."""
        # Check if belief is based on foundational beliefs
        return len(belief.justification_chain) > 0 and len(belief.supporting_evidence) > 0

    def _validate_reliability(self, belief: Belief) -> bool:
        """Validate belief using reliabilist criteria."""
        # Check if belief formation process is reliable
        return belief.confidence > 0.7 and len(belief.supporting_evidence) >= len(belief.counter_evidence)

    def _assess_coherence_strength(self, belief: Belief) -> float:
        """Assess coherence strength."""
        coherence_count = sum(1 for other in self.beliefs.values()
                            if other != belief and self._beliefs_coherent(belief, other))
        return coherence_count / max(1, len(self.beliefs) - 1)

    def _assess_foundational_strength(self, belief: Belief) -> float:
        """Assess foundational strength."""
        chain_length = len(belief.justification_chain)
        evidence_ratio = len(belief.supporting_evidence) / max(1, len(belief.supporting_evidence) + len(belief.counter_evidence))
        return min(1.0, (chain_length * 0.3 + evidence_ratio * 0.7))

    def _assess_reliability_strength(self, belief: Belief) -> float:
        """Assess reliability strength."""
        return belief.confidence

    def _beliefs_coherent(self, belief1: Belief, belief2: Belief) -> bool:
        """Check if two beliefs are coherent."""
        # Simplified coherence check - in practice would use semantic similarity
        return abs(belief1.confidence - belief2.confidence) < 0.5

    def evaluate_epistemic_virtue(self, agent_actions: List[Dict[str, Any]]) -> Dict[str, float]:
        """Evaluate epistemic virtues based on agent actions."""
        virtue_scores = {virtue: 0.0 for virtue in self.epistemic_virtues}

        for action in agent_actions:
            action_type = action.get("type", "")

            if action_type == "question_asked":
                virtue_scores["curiosity"] += 1.0
            elif action_type == "belief_revised":
                virtue_scores["open_mindedness"] += 1.0
            elif action_type == "evidence_sought":
                virtue_scores["intellectual_courage"] += 1.0
            elif action_type == "independent_judgment":
                virtue_scores["intellectual_autonomy"] += 1.0

        # Normalize scores
        total_actions = len(agent_actions)
        if total_actions > 0:
            for virtue in virtue_scores:
                virtue_scores[virtue] /= total_actions

        return virtue_scores

    def detect_epistemic_bias(self, belief_system: Dict[str, Belief]) -> List[Dict[str, Any]]:
        """Detect potential epistemic biases in belief system."""
        biases = []

        # Check for confirmation bias
        confirmation_indicators = []
        for belief_id, belief in belief_system.items():
            supporting_ratio = len(belief.supporting_evidence) / max(1, len(belief.supporting_evidence) + len(belief.counter_evidence))
            if supporting_ratio > 0.8:
                confirmation_indicators.append(belief_id)

        if len(confirmation_indicators) > len(belief_system) * 0.7:
            biases.append({
                "bias_type": "confirmation_bias",
                "severity": "high",
                "affected_beliefs": confirmation_indicators
            })

        # Check for anchoring bias
        initial_confidences = [b.confidence for b in belief_system.values()]
        if initial_confidences and max(initial_confidences) - min(initial_confidences) < 0.1:
            biases.append({
                "bias_type": "anchoring_bias",
                "severity": "medium",
                "description": "Beliefs have very similar confidence levels"
            })

        return biases

    def get_epistemological_profile(self) -> Dict[str, Any]:
        """Get epistemological profile of the framework."""
        return {
            "primary_theory": self.primary_theory.value,
            "available_theories": list(self.justification_theories.keys()),
            "total_beliefs": len(self.beliefs),
            "epistemic_virtues": list(self.epistemic_virtues),
            "average_confidence": sum(b.confidence for b in self.beliefs.values()) / max(1, len(self.beliefs))
        }