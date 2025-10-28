# LOGOS Core - Proof-gated alignment components

from .archon_planner import ArchonPlannerGate
from .integration_harmonizer import IntegrationHarmonizer
from .logos_nexus import LogosNexus
from .reference_monitor import ReferenceMonitor, ProofGateError, KernelHashMismatchError
from .pxl_client import PXLClient
from .unified_formalisms import UnifiedFormalismValidator
from ..learning.autonomous_learning import LearningCycleManager
from .meta_reasoning.iel_generator import IELGenerator
from .meta_reasoning.iel_evaluator import IELEvaluator
from .meta_reasoning.iel_registry import IELRegistry
from ..language.natural_language_processor import NaturalLanguageProcessor
from .runtime.iel_runtime_interface import ModalLogicEvaluator
from ..iel_integration import get_iel_integration, initialize_iel_system, IELIntegration

__all__ = [
    'ArchonPlannerGate',
    'IntegrationHarmonizer',
    'LogosNexus',
    'ReferenceMonitor',
    'ProofGateError',
    'KernelHashMismatchError',
    'PXLClient',
    'UnifiedFormalismValidator',
    'LearningCycleManager',
    'IELGenerator',
    'IELEvaluator',
    'IELRegistry',
    'NaturalLanguageProcessor',
    'ModalLogicEvaluator',
    'IELIntegration',
    'get_iel_integration',
    'initialize_iel_system'
]
