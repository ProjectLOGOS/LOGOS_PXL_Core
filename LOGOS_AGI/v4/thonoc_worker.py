# logos_agi_v1/subsystems/thonoc/thonoc_worker.py

"""
THONOC Logical Reasoning Worker

The Logician - handles formal reasoning, proof construction, modal logic,
consequence assignment, and axiomatic validation.

Responsibilities:
- Formal proof construction and verification
- Modal logic reasoning (necessity, possibility)
- Consequence assignment and moral reasoning
- Axiomatic system validation
- Lambda calculus evaluation
- Logical consistency checking
"""

import os
import sys
import json
import time
import logging
import signal
import uuid
from typing import Dict, List, Any, Optional, Tuple, Union
from datetime import datetime
from enum import Enum

# RabbitMQ and messaging
import pika

# Core LOGOS imports
try:
    from core.logic.axiomatic_proof_engine import AxiomaticProofEngine
    from core.logic.lambda_engine import LambdaEngine
    from core.logic.modal_inference_engine import ModalInferenceEngine
    from core.data_structures import TaskDescriptor, OperationResult
except ImportError:
    # Fallback implementations if core modules aren't available
    pass

# Configuration
SUBSYSTEM_NAME = "THONOC"
RABBITMQ_HOST = os.getenv('RABBITMQ_HOST', 'rabbitmq')
RABBITMQ_PORT = int(os.getenv('RABBITMQ_PORT', '5672'))
TASK_QUEUE = 'thonoc_task_queue'
RESULT_QUEUE = 'task_result_queue'

# Logging setup
logging.basicConfig(
    level=logging.INFO,
    format=f'%(asctime)s - %(levelname)s - {SUBSYSTEM_NAME}_WORKER - %(message)s',
    handlers=[
        logging.StreamHandler(sys.stdout),
        logging.FileHandler('/app/logs/thonoc_worker.log', mode='a')
    ]
)

class ModalOperator(Enum):
    """Modal logic operators."""
    NECESSARY = "□"      # Necessarily
    POSSIBLE = "◊"       # Possibly
    KNOWN = "K"          # Known that
    BELIEVED = "B"       # Believed that

class LogicalConnective(Enum):
    """Standard logical connectives."""
    AND = "∧"
    OR = "∨"
    NOT = "¬"
    IMPLIES = "→"
    IFF = "↔"
    FORALL = "∀"
    EXISTS = "∃"

class ProofStatus(Enum):
    """Status of proof construction attempts."""
    PROVEN = "proven"
    DISPROVEN = "disproven"
    UNDECIDABLE = "undecidable"
    INSUFFICIENT_AXIOMS = "insufficient_axioms"
    INVALID_FORMULA = "invalid_formula"

class LambdaEngineImplementation:
    """
    Lambda calculus engine for formal logical expression evaluation.
    Provides parsing, type checking, and evaluation of lambda expressions.
    """

    def __init__(self):
        self.logger = logging.getLogger("LAMBDA_ENGINE")
        self.type_environment = {}
        self.axiom_base = self._initialize_axiom_base()

    def _initialize_axiom_base(self) -> Dict[str, str]:
        """Initialize the foundational axiom base for logical reasoning."""
        return {
            'axiom_identity': 'λx.x',
            'axiom_composition': 'λf.λg.λx.f(g(x))',
            'axiom_conjunction': 'λp.λq.λx.(p(x) ∧ q(x))',
            'axiom_disjunction': 'λp.λq.λx.(p(x) ∨ q(x))',
            'axiom_negation': 'λp.λx.¬p(x)',
            'axiom_implication': 'λp.λq.λx.(p(x) → q(x))',
            'modus_ponens': 'λp.λq.((p ∧ (p → q)) → q)',
            'law_excluded_middle': 'λp.(p ∨ ¬p)',
            'law_contradiction': 'λp.¬(p ∧ ¬p)'
        }

    def parse(self, expression: str) -> Dict[str, Any]:
        """
        Parse a lambda expression into an abstract syntax tree.
        Simplified parsing for demonstration purposes.
        """
        try:
            expression = expression.strip()

            if expression.startswith('λ'):
                # Lambda abstraction
                parts = expression[1:].split('.', 1)
                if len(parts) == 2:
                    variable = parts[0].strip()
                    body = parts[1].strip()
                    return {
                        'type': 'abstraction',
                        'variable': variable,
                        'body': self.parse(body)
                    }

            elif '(' in expression and ')' in expression:
                # Application or compound expression
                # Simple parsing - find main operator
                inner = expression.strip('()')

                # Check for logical operators
                for op in ['∧', '∨', '→', '↔']:
                    if op in inner:
                        parts = inner.split(op, 1)
                        if len(parts) == 2:
                            return {
                                'type': 'binary_operation',
                                'operator': op,
                                'left': self.parse(parts[0].strip()),
                                'right': self.parse(parts[1].strip())
                            }

                # Check for modal operators
                for modal in ['□', '◊', 'K', 'B']:
                    if inner.startswith(modal):
                        return {
                            'type': 'modal_operation',
                            'operator': modal,
                            'operand': self.parse(inner[1:].strip())
                        }

                # Function application
                if ' ' in inner:
                    parts = inner.split(' ', 1)
                    return {
                        'type': 'application',
                        'function': self.parse(parts[0].strip()),
                        'argument': self.parse(parts[1].strip())
                    }

            elif expression.startswith('¬'):
                # Negation
                return {
                    'type': 'negation',
                    'operand': self.parse(expression[1:].strip())
                }

            # Atomic proposition or variable
            return {
                'type': 'atom',
                'value': expression
            }

        except Exception as e:
            self.logger.error(f"Parsing error: {e}")
            return {
                'type': 'error',
                'message': str(e),
                'expression': expression
            }

    def evaluate(self, parsed_expr: Dict[str, Any], context: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        """
        Evaluate a parsed lambda expression in the given context.
        """
        context = context or {}

        try:
            expr_type = parsed_expr.get('type')

            if expr_type == 'atom':
                value = parsed_expr.get('value')
                if value in context:
                    return context[value]
                elif value in self.axiom_base:
                    return self.parse(self.axiom_base[value])
                else:
                    return parsed_expr

            elif expr_type == 'abstraction':
                # Lambda abstraction - return as function
                return {
                    'type': 'function',
                    'parameter': parsed_expr.get('variable'),
                    'body': parsed_expr.get('body'),
                    'context': context.copy()
                }

            elif expr_type == 'application':
                function = self.evaluate(parsed_expr.get('function'), context)
                argument = self.evaluate(parsed_expr.get('argument'), context)

                if function.get('type') == 'function':
                    # Beta reduction
                    param = function.get('parameter')
                    body = function.get('body')
                    func_context = function.get('context', {})

                    # Substitute argument for parameter in body
                    new_context = {**func_context, param: argument}
                    return self.evaluate(body, new_context)

                return {
                    'type': 'application_result',
                    'function': function,
                    'argument': argument
                }

            elif expr_type == 'binary_operation':
                left = self.evaluate(parsed_expr.get('left'), context)
                right = self.evaluate(parsed_expr.get('right'), context)
                operator = parsed_expr.get('operator')

                return {
                    'type': 'binary_result',
                    'operator': operator,
                    'left': left,
                    'right': right,
                    'truth_value': self._evaluate_binary_operation(left, right, operator)
                }

            elif expr_type == 'modal_operation':
                operand = self.evaluate(parsed_expr.get('operand'), context)
                operator = parsed_expr.get('operator')

                return {
                    'type': 'modal_result',
                    'operator': operator,
                    'operand': operand,
                    'truth_value': self._evaluate_modal_operation(operand, operator, context)
                }

            elif expr_type == 'negation':
                operand = self.evaluate(parsed_expr.get('operand'), context)
                truth_value = not self._extract_truth_value(operand)

                return {
                    'type': 'negation_result',
                    'operand': operand,
                    'truth_value': truth_value
                }

            else:
                return parsed_expr

        except Exception as e:
            self.logger.error(f"Evaluation error: {e}")
            return {
                'type': 'error',
                'message': str(e),
                'expression': parsed_expr
            }

    def _evaluate_binary_operation(self, left: Dict[str, Any], right: Dict[str, Any], operator: str) -> Optional[bool]:
        """Evaluate binary logical operations."""
        left_truth = self._extract_truth_value(left)
        right_truth = self._extract_truth_value(right)

        if left_truth is None or right_truth is None:
            return None

        if operator == '∧':
            return left_truth and right_truth
        elif operator == '∨':
            return left_truth or right_truth
        elif operator == '→':
            return not left_truth or right_truth
        elif operator == '↔':
            return left_truth == right_truth
        else:
            return None

    def _evaluate_modal_operation(self, operand: Dict[str, Any], operator: str, context: Dict[str, Any]) -> Optional[bool]:
        """Evaluate modal operations."""
        operand_truth = self._extract_truth_value(operand)

        if operator == '□':  # Necessarily
            # In possible worlds semantics, necessarily true means true in all possible worlds
            # Simplified: if it's true and follows from axioms, it's necessary
            return operand_truth and self._is_derivable_from_axioms(operand)
        elif operator == '◊':  # Possibly
            # Possibly true means true in at least one possible world
            return operand_truth or not self._leads_to_contradiction(operand)
        elif operator == 'K':  # Known
            # Known means derivable from current knowledge base
            return self._is_derivable_from_axioms(operand)
        elif operator == 'B':  # Believed
            # Believed means consistent with current beliefs (simplified)
            return not self._leads_to_contradiction(operand)
        else:
            return None

    def _extract_truth_value(self, expr: Dict[str, Any]) -> Optional[bool]:
        """Extract truth value from an evaluated expression."""
        if expr.get('truth_value') is not None:
            return expr.get('truth_value')
        elif expr.get('type') == 'atom':
            value = expr.get('value')
            if value in ['true', 'True', '⊤']:
                return True
            elif value in ['false', 'False', '⊥']:
                return False
        return None

    def _is_derivable_from_axioms(self, expr: Dict[str, Any]) -> bool:
        """Check if expression is derivable from axioms (simplified)."""
        # Simplified derivability check
        if expr.get('type') == 'atom':
            return expr.get('value') in self.axiom_base
        return False

    def _leads_to_contradiction(self, expr: Dict[str, Any]) -> bool:
        """Check if expression leads to logical contradiction (simplified)."""
        # Simplified contradiction check
        return False

class AxiomaticProofEngineImplementation:
    """
    Axiomatic proof engine for constructing formal proofs from axioms.
    Provides proof construction, validation, and theorem proving capabilities.
    """

    def __init__(self, lambda_engine: LambdaEngineImplementation):
        self.logger = logging.getLogger("PROOF_ENGINE")
        self.lambda_engine = lambda_engine
        self.axioms = self._load_axioms()
        self.proven_theorems = set()

    def _load_axioms(self) -> Dict[str, Dict[str, Any]]:
        """Load foundational axioms for proof construction."""
        return {
            'axiom_identity': {
                'statement': 'λx.x',
                'description': 'Identity function',
                'type': 'logical_axiom'
            },
            'axiom_modus_ponens': {
                'statement': '((p ∧ (p → q)) → q)',
                'description': 'Modus ponens inference rule',
                'type': 'inference_rule'
            },
            'axiom_excluded_middle': {
                'statement': '(p ∨ ¬p)',
                'description': 'Law of excluded middle',
                'type': 'logical_axiom'
            },
            'axiom_non_contradiction': {
                'statement': '¬(p ∧ ¬p)',
                'description': 'Law of non-contradiction',
                'type': 'logical_axiom'
            },
            'axiom_distribution': {
                'statement': '(p ∧ (q ∨ r)) ↔ ((p ∧ q) ∨ (p ∧ r))',
                'description': 'Distribution of conjunction over disjunction',
                'type': 'logical_axiom'
            }
        }

    def construct_proof(self, claim: str, counter_claims: List[str] = None) -> Dict[str, Any]:
        """
        Construct a formal proof for the given claim.
        Attempts to prove the claim and disprove counter-claims.
        """
        try:
            self.logger.info(f"Constructing proof for claim: {claim}")

            # Parse the claim
            parsed_claim = self.lambda_engine.parse(claim)

            if parsed_claim.get('type') == 'error':
                return {
                    'status': ProofStatus.INVALID_FORMULA.value,
                    'claim': claim,
                    'error': parsed_claim.get('message'),
                    'proof_steps': []
                }

            # Attempt to construct proof
            proof_result = self._attempt_proof_construction(parsed_claim, claim)

            # Handle counter-claims if provided
            counter_results = []
            if counter_claims:
                for counter_claim in counter_claims:
                    counter_result = self._evaluate_counter_claim(counter_claim, claim)
                    counter_results.append(counter_result)

            # Determine overall proof status
            overall_status = self._determine_proof_status(proof_result, counter_results)

            return {
                'status': overall_status,
                'claim': claim,
                'proof_steps': proof_result.get('steps', []),
                'axioms_used': proof_result.get('axioms_used', []),
                'counter_claim_results': counter_results,
                'confidence': proof_result.get('confidence', 0.5),
                'reasoning': proof_result.get('reasoning', ''),
                'formal_representation': str(parsed_claim)
            }

        except Exception as e:
            self.logger.error(f"Proof construction failed: {e}")
            return {
                'status': ProofStatus.INVALID_FORMULA.value,
                'claim': claim,
                'error': str(e),
                'proof_steps': []
            }

    def _attempt_proof_construction(self, parsed_claim: Dict[str, Any], original_claim: str) -> Dict[str, Any]:
        """Attempt to construct a proof for the parsed claim."""
        proof_steps = []
        axioms_used = []

        # Step 1: Check if claim is already an axiom
        if self._is_axiom(parsed_claim):
            axiom_name = self._find_matching_axiom(parsed_claim)
            proof_steps.append({
                'step': 1,
                'statement': original_claim,
                'justification': f'Axiom: {axiom_name}',
                'rule': 'axiom'
            })
            axioms_used.append(axiom_name)

            return {
                'status': ProofStatus.PROVEN.value,
                'steps': proof_steps,
                'axioms_used': axioms_used,
                'confidence': 1.0,
                'reasoning': 'Claim is a direct axiom of the system'
            }

        # Step 2: Try to derive from axioms using simple inference rules
        derivation_result = self._attempt_derivation(parsed_claim, original_claim)

        if derivation_result['success']:
            proof_steps.extend(derivation_result['steps'])
            axioms_used.extend(derivation_result['axioms_used'])

            return {
                'status': ProofStatus.PROVEN.value,
                'steps': proof_steps,
                'axioms_used': axioms_used,
                'confidence': derivation_result['confidence'],
                'reasoning': derivation_result['reasoning']
            }

        # Step 3: Check for consistency with axioms
        consistency_check = self._check_consistency(parsed_claim)

        if not consistency_check['consistent']:
            return {
                'status': ProofStatus.DISPROVEN.value,
                'steps': [{
                    'step': 1,
                    'statement': original_claim,
                    'justification': 'Leads to contradiction with axioms',
                    'rule': 'contradiction'
                }],
                'axioms_used': consistency_check['conflicting_axioms'],
                'confidence': 0.9,
                'reasoning': 'Claim contradicts fundamental axioms'
            }

        # Step 4: If we can't prove or disprove, it's undecidable with current axioms
        return {
            'status': ProofStatus.UNDECIDABLE.value,
            'steps': [{
                'step': 1,
                'statement': original_claim,
                'justification': 'Cannot be proven or disproven with current axiom set',
                'rule': 'undecidable'
            }],
            'axioms_used': [],
            'confidence': 0.3,
            'reasoning': 'Claim is independent of the current axiom system'
        }

    def _is_axiom(self, parsed_expr: Dict[str, Any]) -> bool:
        """Check if the expression matches any known axiom."""
        for axiom_name, axiom_data in self.axioms.items():
            axiom_parsed = self.lambda_engine.parse(axiom_data['statement'])
            if self._expressions_equivalent(parsed_expr, axiom_parsed):
                return True
        return False

    def _find_matching_axiom(self, parsed_expr: Dict[str, Any]) -> Optional[str]:
        """Find the name of the axiom that matches the expression."""
        for axiom_name, axiom_data in self.axioms.items():
            axiom_parsed = self.lambda_engine.parse(axiom_data['statement'])
            if self._expressions_equivalent(parsed_expr, axiom_parsed):
                return axiom_name
        return None

    def _expressions_equivalent(self, expr1: Dict[str, Any], expr2: Dict[str, Any]) -> bool:
        """Check if two parsed expressions are logically equivalent (simplified)."""
        # Simplified equivalence check
        return str(expr1) == str(expr2)

    def _attempt_derivation(self, parsed_claim: Dict[str, Any], original_claim: str) -> Dict[str, Any]:
        """Attempt to derive the claim from axioms using inference rules."""
        # Simplified derivation attempt

        # Check if claim follows from modus ponens
        if parsed_claim.get('type') == 'binary_operation' and parsed_claim.get('operator') == '→':
            # For implications, check if we can derive the consequent from the antecedent
            antecedent = parsed_claim.get('left')
            consequent = parsed_claim.get('right')

            # If antecedent is an axiom or proven theorem, we can derive the consequent
            if self._is_axiom(antecedent) or str(antecedent) in self.proven_theorems:
                steps = [
                    {
                        'step': 1,
                        'statement': str(antecedent),
                        'justification': 'Axiom' if self._is_axiom(antecedent) else 'Previously proven theorem',
                        'rule': 'axiom'
                    },
                    {
                        'step': 2,
                        'statement': original_claim,
                        'justification': 'Given implication structure',
                        'rule': 'implication_introduction'
                    }
                ]

                return {
                    'success': True,
                    'steps': steps,
                    'axioms_used': ['axiom_modus_ponens'],
                    'confidence': 0.8,
                    'reasoning': 'Derived using implication rules'
                }

        # Check if claim is a tautology (always true)
        if self._is_tautology(parsed_claim):
            steps = [{
                'step': 1,
                'statement': original_claim,
                'justification': 'Logical tautology',
                'rule': 'tautology'
            }]

            return {
                'success': True,
                'steps': steps,
                'axioms_used': ['axiom_excluded_middle'],
                'confidence': 1.0,
                'reasoning': 'Claim is a logical tautology'
            }

        return {
            'success': False,
            'steps': [],
            'axioms_used': [],
            'confidence': 0.0,
            'reasoning': 'No derivation path found'
        }

    def _is_tautology(self, parsed_expr: Dict[str, Any]) -> bool:
        """Check if expression is a tautology (simplified)."""
        # Check for patterns like (p ∨ ¬p)
        if (parsed_expr.get('type') == 'binary_operation' and
            parsed_expr.get('operator') == '∨'):

            left = parsed_expr.get('left')
            right = parsed_expr.get('right')

            # Check if right is negation of left
            if (right.get('type') == 'negation' and
                self._expressions_equivalent(left, right.get('operand'))):
                return True

        return False

    def _check_consistency(self, parsed_expr: Dict[str, Any]) -> Dict[str, Any]:
        """Check if expression is consistent with axioms."""
        # Simplified consistency check
        # Look for patterns that would contradict basic axioms

        if (parsed_expr.get('type') == 'binary_operation' and
            parsed_expr.get('operator') == '∧'):

            left = parsed_expr.get('left')
            right = parsed_expr.get('right')

            # Check for (p ∧ ¬p) pattern
            if (right.get('type') == 'negation' and
                self._expressions_equivalent(left, right.get('operand'))):
                return {
                    'consistent': False,
                    'conflicting_axioms': ['axiom_non_contradiction'],
                    'reason': 'Violates law of non-contradiction'
                }

        return {
            'consistent': True,
            'conflicting_axioms': [],
            'reason': 'No contradictions found'
        }

    def _evaluate_counter_claim(self, counter_claim: str, original_claim: str) -> Dict[str, Any]:
        """Evaluate a counter-claim against the original claim."""
        try:
            parsed_counter = self.lambda_engine.parse(counter_claim)

            # Simple evaluation: if counter-claim contradicts original claim
            if self._claims_contradict(counter_claim, original_claim):
                return {
                    'counter_claim': counter_claim,
                    'contradicts_main_claim': True,
                    'status': 'refuted',
                    'reasoning': 'Counter-claim directly contradicts main claim'
                }
            else:
                return {
                    'counter_claim': counter_claim,
                    'contradicts_main_claim': False,
                    'status': 'compatible',
                    'reasoning': 'Counter-claim is compatible with main claim'
                }

        except Exception as e:
            return {
                'counter_claim': counter_claim,
                'status': 'invalid',
                'error': str(e),
                'reasoning': 'Counter-claim has invalid syntax'
            }

    def _claims_contradict(self, claim1: str, claim2: str) -> bool:
        """Check if two claims contradict each other (simplified)."""
        # Simple contradiction detection
        if claim1.strip() == f"¬({claim2.strip()})":
            return True
        if claim2.strip() == f"¬({claim1.strip()})":
            return True
        return False

    def _determine_proof_status(self, proof_result: Dict[str, Any], counter_results: List[Dict[str, Any]]) -> str:
        """Determine overall proof status based on main proof and counter-claims."""
        main_status = proof_result.get('status', ProofStatus.UNDECIDABLE.value)

        # If main claim is disproven, overall status is disproven
        if main_status == ProofStatus.DISPROVEN.value:
            return ProofStatus.DISPROVEN.value

        # If any counter-claim contradicts and is valid, main claim is questionable
        for counter_result in counter_results:
            if (counter_result.get('contradicts_main_claim') and
                counter_result.get('status') != 'invalid'):
                return ProofStatus.UNDECIDABLE.value

        return main_status

class ModalInferenceEngineImplementation:
    """
    Modal inference engine for reasoning about necessity, possibility,
    knowledge, and belief using modal logic.
    """

    def __init__(self, lambda_engine: LambdaEngineImplementation):
        self.logger = logging.getLogger("MODAL_ENGINE")
        self.lambda_engine = lambda_engine
        self.possible_worlds = self._initialize_possible_worlds()
        self.accessibility_relation = self._initialize_accessibility()

    def _initialize_possible_worlds(self) -> Dict[str, Dict[str, Any]]:
        """Initialize possible worlds for modal reasoning."""
        return {
            'actual_world': {
                'propositions': set(),
                'properties': {'actual': True, 'accessible': True}
            },
            'ideal_world': {
                'propositions': set(),
                'properties': {'ideal': True, 'accessible': True}
            },
            'minimal_world': {
                'propositions': set(),
                'properties': {'minimal': True, 'accessible': True}
            }
        }

    def _initialize_accessibility(self) -> Dict[str, List[str]]:
        """Initialize accessibility relations between worlds."""
        return {
            'actual_world': ['actual_world', 'ideal_world', 'minimal_world'],
            'ideal_world': ['ideal_world'],
            'minimal_world': ['minimal_world', 'actual_world']
        }

    def assign_consequence(self, outcome: Dict[str, Any], context: Dict[str, Any] = None) -> Dict[str, Any]:
        """
        Assign modal consequences to outcomes based on their properties.
        Determines necessity, possibility, and moral implications.
        """
        try:
            outcome_description = outcome.get('description', '')
            outcome_probability = outcome.get('probability', 0.5)
            outcome_type = outcome.get('type', 'general')
            moral_alignment = outcome.get('alignment', 'neutral')

            # Modal analysis
            modal_analysis = self._analyze_modal_properties(outcome_probability, outcome_type)

            # Moral consequence assignment
            moral_consequences = self._assign_moral_consequences(moral_alignment, outcome_description)

            # Logical consequence derivation
            logical_consequences = self._derive_logical_consequences(outcome, context or {})

            # Overall consequence assessment
            consequence_severity = self._assess_consequence_severity(outcome, modal_analysis, moral_consequences)

            return {
                'status': 'success',
                'outcome': outcome,
                'modal_analysis': modal_analysis,
                'moral_consequences': moral_consequences,
                'logical_consequences': logical_consequences,
                'consequence_severity': consequence_severity,
                'recommendation': self._generate_recommendation(consequence_severity, modal_analysis)
            }

        except Exception as e:
            self.logger.error(f"Consequence assignment failed: {e}")
            return {
                'status': 'error',
                'error': str(e),
                'outcome': outcome
            }

    def _analyze_modal_properties(self, probability: float, outcome_type: str) -> Dict[str, Any]:
        """Analyze modal properties (necessity, possibility) of an outcome."""
        # Necessity analysis
        is_necessary = probability >= 0.95  # Very high probability outcomes are necessary
        is_possible = probability > 0.0     # Any non-zero probability is possible
        is_contingent = 0.05 < probability < 0.95  # Outcomes that could go either way
        is_impossible = probability == 0.0  # Zero probability outcomes are impossible

        # Modal strength assessment
        if is_necessary:
            modal_strength = 'necessary'
            modal_operator = ModalOperator.NECESSARY.value
        elif is_impossible:
            modal_strength = 'impossible'
            modal_operator = f"{LogicalConnective.NOT.value}{ModalOperator.POSSIBLE.value}"
        elif is_contingent:
            modal_strength = 'contingent'
            modal_operator = f"{ModalOperator.POSSIBLE.value}{LogicalConnective.AND.value}{ModalOperator.POSSIBLE.value}{LogicalConnective.NOT.value}"
        else:
            modal_strength = 'possible'
            modal_operator = ModalOperator.POSSIBLE.value

        return {
            'necessity': is_necessary,
            'possibility': is_possible,
            'contingency': is_contingent,
            'impossibility': is_impossible,
            'modal_strength': modal_strength,
            'modal_operator': modal_operator,
            'probability': probability,
            'certainty_level': 'high' if probability > 0.8 or probability < 0.2 else 'medium' if probability > 0.6 or probability < 0.4 else 'low'
        }

    def _assign_moral_consequences(self, alignment: str, description: str) -> Dict[str, Any]:
        """Assign moral consequences based on outcome alignment."""
        moral_weight = 0.0
        moral_category = 'neutral'
        ethical_implications = []

        if alignment == 'positive' or 'good' in description.lower():
            moral_weight = 0.8
            moral_category = 'virtuous'
            ethical_implications = ['Promotes wellbeing', 'Increases good in the world']
        elif alignment == 'negative' or 'harm' in description.lower():
            moral_weight = -0.8
            moral_category = 'harmful'
            ethical_implications = ['Causes harm', 'Decreases overall wellbeing']
        elif alignment == 'mixed':
            moral_weight = 0.0
            moral_category = 'complex'
            ethical_implications = ['Mixed moral implications', 'Requires careful consideration']
        else:
            moral_weight = 0.0
            moral_category = 'neutral'
            ethical_implications = ['No significant moral implications']

        # Determine moral obligation
        if moral_weight > 0.5:
            moral_obligation = 'ought to pursue'
        elif moral_weight < -0.5:
            moral_obligation = 'ought to prevent'
        else:
            moral_obligation = 'morally permissible'

        return {
            'moral_weight': moral_weight,
            'moral_category': moral_category,
            'ethical_implications': ethical_implications,
            'moral_obligation': moral_obligation,
            'alignment': alignment
        }

    def _derive_logical_consequences(self, outcome: Dict[str, Any], context: Dict[str, Any]) -> Dict[str, Any]:
        """Derive logical consequences from the outcome and context."""
        logical_implications = []
        causal_connections = []
        conditional_consequences = []

        # Extract logical patterns from outcome description
        description = outcome.get('description', '').lower()

        # Simple logical pattern recognition
        if 'if' in description and 'then' in description:
            conditional_consequences.append('Conditional relationship identified')

        if 'causes' in description or 'leads to' in description:
            causal_connections.append('Causal relationship implied')

        if 'prevents' in description or 'stops' in description:
            logical_implications.append('Preventive action identified')

        # Context-based implications
        for key, value in context.items():
            if isinstance(value, str) and any(word in value.lower() for word in ['affect', 'influence', 'impact']):
                logical_implications.append(f'Interaction with {key} context')

        return {
            'logical_implications': logical_implications,
            'causal_connections': causal_connections,
            'conditional_consequences': conditional_consequences,
            'logical_strength': len(logical_implications) + len(causal_connections)
        }

    def _assess_consequence_severity(self, outcome: Dict[str, Any], modal_analysis: Dict[str, Any], moral_consequences: Dict[str, Any]) -> Dict[str, Any]:
        """Assess the overall severity of consequences."""
        severity_score = 0.0

        # Modal contribution to severity
        if modal_analysis.get('necessity'):
            severity_score += 0.4  # Necessary outcomes are more severe
        elif modal_analysis.get('possibility'):
            severity_score += 0.2  # Possible outcomes have moderate severity

        # Moral contribution to severity
        moral_weight = abs(moral_consequences.get('moral_weight', 0))
        severity_score += moral_weight * 0.6

        # Probability contribution
        probability = outcome.get('probability', 0.5)
        if probability > 0.8 or probability < 0.2:
            severity_score += 0.3  # High certainty increases severity

        # Determine severity level
        if severity_score > 0.8:
            severity_level = 'critical'
        elif severity_score > 0.6:
            severity_level = 'high'
        elif severity_score > 0.4:
            severity_level = 'medium'
        else:
            severity_level = 'low'

        return {
            'severity_score': min(1.0, severity_score),
            'severity_level': severity_level,
            'contributing_factors': [
                f"Modal strength: {modal_analysis.get('modal_strength')}",
                f"Moral weight: {moral_consequences.get('moral_weight')}",
                f"Probability: {probability}"
            ]
        }

    def _generate_recommendation(self, consequence_severity: Dict[str, Any], modal_analysis: Dict[str, Any]) -> Dict[str, Any]:
        """Generate action recommendations based on consequence analysis."""
        severity_level = consequence_severity.get('severity_level')
        modal_strength = modal_analysis.get('modal_strength')

        if severity_level == 'critical':
            if modal_strength == 'necessary':
                recommendation = 'Immediate action required - outcome is inevitable'
                urgency = 'immediate'
            else:
                recommendation = 'High priority intervention needed'
                urgency = 'high'
        elif severity_level == 'high':
            recommendation = 'Significant attention and planning required'
            urgency = 'medium'
        elif severity_level == 'medium':
            recommendation = 'Monitor and prepare contingencies'
            urgency = 'low'
        else:
            recommendation = 'No immediate action required'
            urgency = 'none'

        return {
            'recommendation': recommendation,
            'urgency': urgency,
            'confidence': 0.75,
            'basis': f'Severity: {severity_level}, Modal: {modal_strength}'
        }

class ThonocCoreEngine:
    """
    Core logic engine for THONOC subsystem.
    Orchestrates formal reasoning, proof construction, and modal logic operations.
    """

    def __init__(self):
        self.logger = logging.getLogger("THONOC_CORE")
        self.worker_id = f"thonoc_{uuid.uuid4().hex[:8]}"

        # Initialize logical reasoning components
        self.lambda_engine = LambdaEngineImplementation()
        self.proof_engine = AxiomaticProofEngineImplementation(self.lambda_engine)
        self.modal_engine = ModalInferenceEngineImplementation(self.lambda_engine)

        # Proof cache for performance
        self.proof_cache = {}
        self.theorem_database = set()

        self.logger.info(f"THONOC Core Engine initialized with worker ID: {self.worker_id}")

    def execute(self, task_type: str, payload: Dict[str, Any]) -> Dict[str, Any]:
        """
        Main execution entry point for THONOC tasks.
        Routes tasks to appropriate logical reasoning methods.
        """
        try:
            self.logger.info(f"Executing task type: {task_type}")

            if task_type == 'construct_proof':
                return self._construct_proof(payload)
            elif task_type == 'assign_consequence':
                return self._assign_consequence(payload)
            elif task_type == 'evaluate_lambda':
                return self._evaluate_lambda_expression(payload)
            elif task_type == 'modal_reasoning':
                return self._perform_modal_reasoning(payload)
            elif task_type == 'consistency_check':
                return self._check_logical_consistency(payload)
            elif task_type == 'theorem_proving':
                return self._prove_theorem(payload)
            else:
                return {
                    'status': 'error',
                    'error': f'Unknown task type: {task_type}',
                    'supported_tasks': [
                        'construct_proof', 'assign_consequence', 'evaluate_lambda',
                        'modal_reasoning', 'consistency_check', 'theorem_proving'
                    ]
                }

        except Exception as e:
            self.logger.error(f"Error executing task {task_type}: {e}", exc_info=True)
            return {
                'status': 'error',
                'error': str(e),
                'task_type': task_type
            }

    def _construct_proof(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Construct formal proof for a given claim."""
        try:
            claim = payload.get('claim', '')
            counter_claims = payload.get('counter_claims', [])
            proof_method = payload.get('method', 'axiomatic')

            if not claim:
                return {
                    'status': 'error',
                    'error': 'No claim provided for proof construction'
                }

            # Check cache first
            cache_key = f"{claim}_{hash(tuple(counter_claims))}"
            if cache_key in self.proof_cache:
                cached_result = self.proof_cache[cache_key]
                cached_result['from_cache'] = True
                return cached_result

            # Construct proof using axiomatic method
            if proof_method == 'axiomatic':
                proof_result = self.proof_engine.construct_proof(claim, counter_claims)
            else:
                return {
                    'status': 'error',
                    'error': f'Unsupported proof method: {proof_method}',
                    'supported_methods': ['axiomatic']
                }

            # Cache the result
            self.proof_cache[cache_key] = proof_result

            # If proven, add to theorem database
            if proof_result.get('status') == ProofStatus.PROVEN.value:
                self.theorem_database.add(claim)

            return {
                'status': 'success',
                'proof_result': proof_result,
                'method_used': proof_method,
                'from_cache': False
            }

        except Exception as e:
            return {
                'status': 'error',
                'error': f'Proof construction failed: {str(e)}'
            }

    def _assign_consequence(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Assign modal consequences to outcomes."""
        try:
            outcome = payload.get('outcome', {})
            context = payload.get('context', {})

            if not outcome:
                return {
                    'status': 'error',
                    'error': 'No outcome provided for consequence assignment'
                }

            # Use modal inference engine for consequence assignment
            consequence_result = self.modal_engine.assign_consequence(outcome, context)

            return {
                'status': 'success',
                'consequence_assignment': consequence_result
            }

        except Exception as e:
            return {
                'status': 'error',
                'error': f'Consequence assignment failed: {str(e)}'
            }

    def _evaluate_lambda_expression(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Evaluate lambda calculus expressions."""
        try:
            expression = payload.get('expression', '')
            context = payload.get('context', {})

            if not expression:
                return {
                    'status': 'error',
                    'error': 'No expression provided for evaluation'
                }

            # Parse the expression
            parsed_expr = self.lambda_engine.parse(expression)

            if parsed_expr.get('type') == 'error':
                return {
                    'status': 'error',
                    'error': f'Parsing failed: {parsed_expr.get("message")}',
                    'expression': expression
                }

            # Evaluate the parsed expression
            evaluation_result = self.lambda_engine.evaluate(parsed_expr, context)

            return {
                'status': 'success',
                'original_expression': expression,
                'parsed_expression': parsed_expr,
                'evaluation_result': evaluation_result,
                'context_used': context
            }

        except Exception as e:
            return {
                'status': 'error',
                'error': f'Lambda evaluation failed: {str(e)}'
            }

    def _perform_modal_reasoning(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Perform modal logic reasoning about necessity and possibility."""
        try:
            propositions = payload.get('propositions', [])
            modal_operators = payload.get('modal_operators', [])
            reasoning_type = payload.get('reasoning_type', 'necessity')

            if not propositions:
                return {
                    'status': 'error',
                    'error': 'No propositions provided for modal reasoning'
                }

            modal_results = []

            for i, proposition in enumerate(propositions):
                modal_op = modal_operators[i] if i < len(modal_operators) else ModalOperator.POSSIBLE.value

                # Create modal expression
                modal_expression = f"{modal_op}({proposition})"

                # Parse and evaluate
                parsed_modal = self.lambda_engine.parse(modal_expression)
                evaluation = self.lambda_engine.evaluate(parsed_modal)

                modal_results.append({
                    'proposition': proposition,
                    'modal_operator': modal_op,
                    'modal_expression': modal_expression,
                    'evaluation': evaluation,
                    'truth_value': evaluation.get('truth_value')
                })

            return {
                'status': 'success',
                'reasoning_type': reasoning_type,
                'modal_results': modal_results,
                'total_propositions': len(propositions)
            }

        except Exception as e:
            return {
                'status': 'error',
                'error': f'Modal reasoning failed: {str(e)}'
            }

    def _check_logical_consistency(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Check logical consistency of a set of statements."""
        try:
            statements = payload.get('statements', [])
            consistency_type = payload.get('type', 'pairwise')

            if len(statements) < 2:
                return {
                    'status': 'error',
                    'error': 'At least 2 statements required for consistency checking'
                }

            consistency_results = []
            overall_consistent = True

            if consistency_type == 'pairwise':
                # Check pairwise consistency
                for i in range(len(statements)):
                    for j in range(i + 1, len(statements)):
                        stmt1, stmt2 = statements[i], statements[j]

                        # Simple consistency check
                        consistent = not self._statements_contradict(stmt1, stmt2)

                        consistency_results.append({
                            'statement1': stmt1,
                            'statement2': stmt2,
                            'consistent': consistent,
                            'indices': [i, j]
                        })

                        if not consistent:
                            overall_consistent = False

            return {
                'status': 'success',
                'consistency_type': consistency_type,
                'overall_consistent': overall_consistent,
                'pairwise_results': consistency_results,
                'total_statements': len(statements),
                'inconsistent_pairs': len([r for r in consistency_results if not r['consistent']])
            }

        except Exception as e:
            return {
                'status': 'error',
                'error': f'Consistency checking failed: {str(e)}'
            }

    def _statements_contradict(self, stmt1: str, stmt2: str) -> bool:
        """Check if two statements contradict each other."""
        # Simple contradiction detection
        if stmt1.strip() == f"¬({stmt2.strip()})":
            return True
        if stmt2.strip() == f"¬({stmt1.strip()})":
            return True
        if stmt1.strip() == f"¬{stmt2.strip()}":
            return True
        if stmt2.strip() == f"¬{stmt1.strip()}":
            return True
        return False

    def _prove_theorem(self, payload: Dict[str, Any]) -> Dict[str, Any]:
        """Prove mathematical or logical theorems."""
        try:
            theorem_statement = payload.get('theorem', '')
            axiom_set = payload.get('axioms', [])
            proof_strategy = payload.get('strategy', 'direct')

            if not theorem_statement:
                return {
                    'status': 'error',
                    'error': 'No theorem statement provided'
                }

            # Check if theorem is already proven
            if theorem_statement in self.theorem_database:
                return {
                    'status': 'success',
                    'theorem': theorem_statement,
                    'proof_status': 'already_proven',
                    'strategy_used': 'database_lookup'
                }

            # Attempt to prove the theorem
            if proof_strategy == 'direct':
                proof_result = self.proof_engine.construct_proof(theorem_statement, [])
            else:
                return {
                    'status': 'error',
                    'error': f'Unsupported proof strategy: {proof_strategy}',
                    'supported_strategies': ['direct']
                }

            # Check if proof was successful
            if proof_result.get('status') == ProofStatus.PROVEN.value:
                self.theorem_database.add(theorem_statement)

                return {
                    'status': 'success',
                    'theorem': theorem_statement,
                    'proof_status': 'newly_proven',
                    'proof_details': proof_result,
                    'strategy_used': proof_strategy
                }
            else:
                return {
                    'status': 'success',
                    'theorem': theorem_statement,
                    'proof_status': proof_result.get('status'),
                    'proof_details': proof_result,
                    'strategy_used': proof_strategy
                }

        except Exception as e:
            return {
                'status': 'error',
                'error': f'Theorem proving failed: {str(e)}'
            }

class ThonocWorker:
    """
    Main THONOC worker class that handles RabbitMQ communication
    and orchestrates the core logical reasoning operations.
    """

    def __init__(self):
        self.logger = logging.getLogger("THONOC_WORKER")
        self.core_engine = ThonocCoreEngine()
        self.connection = None
        self.channel = None
        self.is_running = False

        # Setup graceful shutdown handling
        signal.signal(signal.SIGINT, self._signal_handler)
        signal.signal(signal.SIGTERM, self._signal_handler)

        self._connect_to_rabbitmq()
        self.logger.info("THONOC Worker initialized successfully")

    def _connect_to_rabbitmq(self):
        """Establish connection to RabbitMQ with retry logic."""
        max_retries = 10
        retry_delay = 5

        for attempt in range(1, max_retries + 1):
            try:
                credentials = pika.PlainCredentials('guest', 'guest')
                parameters = pika.ConnectionParameters(
                    host=RABBITMQ_HOST,
                    port=RABBITMQ_PORT,
                    credentials=credentials,
                    heartbeat=600,
                    blocked_connection_timeout=300
                )

                self.connection = pika.BlockingConnection(parameters)
                self.channel = self.connection.channel()

                self._setup_queues()

                self.logger.info(f"Successfully connected to RabbitMQ at {RABBITMQ_HOST}:{RABBITMQ_PORT}")
                return

            except pika.exceptions.AMQPConnectionError as e:
                self.logger.warning(f"Attempt {attempt}/{max_retries}: Failed to connect to RabbitMQ: {e}")
                if attempt < max_retries:
                    self.logger.info(f"Retrying in {retry_delay} seconds...")
                    time.sleep(retry_delay)
                else:
                    self.logger.error("Could not connect to RabbitMQ after all attempts. Exiting.")
                    sys.exit(1)
            except Exception as e:
                self.logger.error(f"Unexpected error connecting to RabbitMQ: {e}")
                sys.exit(1)

    def _setup_queues(self):
        """Declare and configure queues."""
        try:
            self.channel.queue_declare(queue=TASK_QUEUE, durable=True)
            self.channel.queue_declare(queue=RESULT_QUEUE, durable=True)
            self.channel.basic_qos(prefetch_count=1)

            self.logger.info(f"Queues configured: {TASK_QUEUE} -> {RESULT_QUEUE}")

        except Exception as e:
            self.logger.error(f"Failed to setup queues: {e}")
            raise

    def process_task(self, ch, method, properties, body):
        """Process incoming task messages."""
        start_time = time.time()
        task_id = "unknown"

        try:
            # Parse message
            task = json.loads(body.decode('utf-8'))
            task_id = task.get('task_id', f'thonoc_{int(time.time() * 1000)}')
            workflow_id = task.get('workflow_id', 'unknown')
            task_type = task.get('type', 'unknown')
            payload = task.get('payload', {})

            self.logger.info(f"Processing task {task_id} (workflow: {workflow_id}) of type: {task_type}")

            # Execute task using core engine
            result_payload = self.core_engine.execute(task_type, payload)
            status = 'success' if result_payload.get('status') == 'success' else 'failure'

            processing_time = time.time() - start_time

            # Prepare response
            response = {
                'subsystem': SUBSYSTEM_NAME,
                'task_id': task_id,
                'workflow_id': workflow_id,
                'status': status,
                'result': result_payload,
                'processing_time': processing_time,
                'timestamp': datetime.utcnow().isoformat()
            }

            # Publish result
            self.channel.basic_publish(
                exchange='',
                routing_key=RESULT_QUEUE,
                body=json.dumps(response),
                properties=pika.BasicProperties(
                    delivery_mode=2,  # Make message persistent
                    correlation_id=task_id
                )
            )

            self.logger.info(f"Task {task_id} completed in {processing_time:.3f}s with status: {status}")

        except json.JSONDecodeError as e:
            self.logger.error(f"Invalid JSON in task {task_id}: {e}")
            self._send_error_response(task_id, f"Invalid JSON: {str(e)}")
        except Exception as e:
            self.logger.error(f"Error processing task {task_id}: {e}", exc_info=True)
            self._send_error_response(task_id, str(e))
        finally:
            # Always acknowledge the message
            try:
                ch.basic_ack(delivery_tag=method.delivery_tag)
            except Exception as e:
                self.logger.error(f"Failed to acknowledge message: {e}")

    def _send_error_response(self, task_id: str, error_message: str):
        """Send error response for failed tasks."""
        try:
            error_response = {
                'subsystem': SUBSYSTEM_NAME,
                'task_id': task_id,
                'status': 'error',
                'error': error_message,
                'timestamp': datetime.utcnow().isoformat()
            }

            self.channel.basic_publish(
                exchange='',
                routing_key=RESULT_QUEUE,
                body=json.dumps(error_response),
                properties=pika.BasicProperties(correlation_id=task_id)
            )
        except Exception as e:
            self.logger.error(f"Failed to send error response: {e}")

    def start_consuming(self):
        """Start consuming messages from the task queue."""
        try:
            self.channel.basic_consume(
                queue=TASK_QUEUE,
                on_message_callback=self.process_task
            )

            self.is_running = True
            self.logger.info(f"{SUBSYSTEM_NAME} Worker started and listening on queue: {TASK_QUEUE}")

            self.channel.start_consuming()

        except KeyboardInterrupt:
            self.logger.info("Received interrupt signal, shutting down gracefully...")
            self._shutdown()
        except Exception as e:
            self.logger.error(f"Error in consumer loop: {e}")
            self._shutdown()

    def _signal_handler(self, signum, frame):
        """Handle system signals for graceful shutdown."""
        self.logger.info(f"Received signal {signum}, initiating shutdown...")
        self._shutdown()

    def _shutdown(self):
        """Gracefully shutdown the worker."""
        if self.is_running:
            self.is_running = False

            # Stop consuming messages
            if self.channel and self.channel.is_open:
                try:
                    self.channel.stop_consuming()
                    self.logger.info("Stopped consuming messages")
                except Exception as e:
                    self.logger.error(f"Error stopping consumer: {e}")

            # Close connections
            if self.connection and self.connection.is_open:
                try:
                    self.connection.close()
                    self.logger.info("RabbitMQ connection closed")
                except Exception as e:
                    self.logger.error(f"Error closing connection: {e}")

            self.logger.info("THONOC Worker shutdown complete")


def main():
    """Main entry point for the THONOC worker."""
    try:
        worker = ThonocWorker()
        worker.start_consuming()
    except Exception as e:
        logging.error(f"Failed to start THONOC worker: {e}")
        sys.exit(1)


if __name__ == '__main__':
    main()
