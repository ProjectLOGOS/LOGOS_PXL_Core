"""
LOGOS Core Entry Point - Global Integration Hub

This module provides the main entry point for the LOGOS AGI system,
integrating the enhanced reference monitor with all reasoning operations.
"""

import os
import sys
import json
import atexit
import logging
from pathlib import Path
from typing import Dict, Any, Optional

# Ensure logos_core is in path
current_dir = Path(__file__).parent
sys.path.insert(0, str(current_dir))

from core.logos_core.reference_monitor import ReferenceMonitor
from safety.integrity_framework.integrity_safeguard import get_global_safety_system, check_operation_safety, emergency_halt
from core.logos_core import get_iel_integration, initialize_iel_system
from core.worker_integration import get_worker_integration, initialize_workers
from core.adaptive_reasoning.bayesian_inference import UnifiedBayesianInferencer
from core.adaptive_reasoning.semantic_transformers import UnifiedSemanticTransformer
from core.logos_core.natural_language_processor import NaturalLanguageProcessor
from core.learning.autonomous_learning import LearningCycleManager

logger = logging.getLogger(__name__)

class LOGOSCore:
    """
    Main LOGOS AGI Core System

    Provides centralized access to all reasoning capabilities with
    integrated reference monitoring and safety guarantees.
    """

    def __init__(self, config: Optional[Dict[str, Any]] = None):
        """
        Initialize LOGOS Core system

        Args:
            config: Optional configuration override
        """
        self.config = config or {}
        self._monitor = None
        self._safety_system = None
        self._initialized = False

        # Setup logging
        self._setup_logging()

        # Initialize reference monitor
        self._initialize_monitor()

        # Initialize safety system
        self._initialize_safety_system()

        # Initialize IEL system
        self._initialize_iel_system()

        # Initialize worker system
        self._initialize_worker_system()

        # Initialize advanced reasoning components
        self._initialize_adaptive_reasoning()

        # Initialize natural language processor
        self._initialize_nlp()

        # Register cleanup
        atexit.register(self.shutdown)

        logger.info("LOGOS Core system initialized with advanced reasoning, NLP, and distributed workers")

    def _setup_logging(self):
        """Setup system logging"""
        log_level = self.config.get('log_level', 'INFO')
        logging.basicConfig(
            level=getattr(logging, log_level),
            format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
        )

    def _initialize_monitor(self):
        """Initialize the reference monitor"""
        try:
            self._monitor = ReferenceMonitor()
            self._initialized = True
            logger.info("Reference Monitor integration successful")
        except Exception as e:
            logger.error(f"Failed to initialize reference monitor: {e}")
            raise

    def _initialize_safety_system(self):
        """Initialize the integrity safeguard system"""
        try:
            self._safety_system = get_global_safety_system()

            # Add violation handler to integrate with monitor
            self._safety_system.add_violation_handler(self._handle_safety_violation)

            logger.info("Integrity Safeguard System integration successful")
        except Exception as e:
            logger.error(f"Failed to initialize safety system: {e}")
            raise

    def _initialize_iel_system(self):
        """Initialize the Internal Extension Libraries system"""
        try:
            self._iel_integration = get_iel_integration()
            iel_success = initialize_iel_system()

            if iel_success:
                logger.info("IEL System integration successful")
            else:
                logger.warning("IEL System partially initialized - some domains may be unavailable")

        except Exception as e:
            logger.error(f"Failed to initialize IEL system: {e}")
            # Don't raise - IEL is optional for core functionality

    def _initialize_worker_system(self):
        """Initialize the distributed worker system"""
        try:
            self._worker_integration = get_worker_integration()
            # Note: Worker initialization is async, will be done when needed
            logger.info("Worker Integration System initialized")
        except Exception as e:
            logger.error(f"Failed to initialize worker system: {e}")
            # Don't raise - workers are optional for core functionality

    def _initialize_adaptive_reasoning(self):
        """Initialize advanced adaptive reasoning components"""
        try:
            self._bayesian_inferencer = UnifiedBayesianInferencer()
            self._semantic_transformer = UnifiedSemanticTransformer()
            logger.info("Adaptive reasoning components initialized")
        except Exception as e:
            logger.error(f"Failed to initialize adaptive reasoning: {e}")
            # Don't raise - adaptive reasoning is optional

    def _initialize_nlp(self):
        """Initialize natural language processor"""
        try:
            self._nlp_processor = NaturalLanguageProcessor()
            logger.info("Natural language processor initialized")
        except Exception as e:
            logger.error(f"Failed to initialize NLP: {e}")
            # Don't raise - NLP is optional

    def _initialize_adaptive_reasoning(self):
        """Initialize advanced adaptive reasoning components"""
        try:
            self._bayesian_inferencer = UnifiedBayesianInferencer()
            self._semantic_transformer = UnifiedSemanticTransformer()
            logger.info("Advanced adaptive reasoning components initialized")
        except Exception as e:
            logger.error(f"Failed to initialize adaptive reasoning: {e}")
            # Don't raise - advanced reasoning is optional

    def _initialize_nlp(self):
        """Initialize natural language processor"""
        try:
            self._nlp_processor = NaturalLanguageProcessor()
            logger.info("Natural language processor initialized")
        except Exception as e:
            logger.error(f"Failed to initialize NLP: {e}")
            # Don't raise - NLP is optional

    def _handle_safety_violation(self, violation):
        """Handle safety violations from the safety system"""
        logger.critical(f"SAFETY VIOLATION: {violation.safeguard_state.name} - {violation.metadata.get('reason', 'Unknown')}")

        # Log the violation - reference monitor blocking not implemented in current version
        logger.warning("Safety violation detected - operations may be restricted")

        # If irreversible, trigger emergency halt
        if not violation.reversible:
            logger.critical("IRREVERSIBLE VIOLATION - TRIGGERING EMERGENCY HALT")
            emergency_halt(f"Safety violation: {violation.safeguard_state.name}")

    @property
    def monitor(self):
        """Access to the reference monitor"""
        if not self._initialized:
            raise RuntimeError("LOGOS Core not initialized")
        return self._monitor

    @property
    def iel(self):
        """Access to the IEL integration system"""
        return getattr(self, '_iel_integration', None)

    @property
    def workers(self):
        """Access to the worker integration system"""
        return getattr(self, '_worker_integration', None)

    @property
    def bayesian(self):
        """Access to the Bayesian inference system"""
        return getattr(self, '_bayesian_inferencer', None)

    @property
    def semantic(self):
        """Access to the semantic transformer system"""
        return getattr(self, '_semantic_transformer', None)

    @property
    def nlp(self):
        """Access to the natural language processor"""
        return getattr(self, '_nlp_processor', None)

    def evaluate_modal_logic(self, proposition: str, **kwargs) -> Dict[str, Any]:
        """
        Evaluate modal logic proposition with full monitoring and safety gates

        Args:
            proposition: Modal logic formula to evaluate
            **kwargs: Additional evaluation parameters

        Returns:
            Evaluation result with monitoring metadata
        """
        if not self._initialized:
            raise RuntimeError("LOGOS Core not initialized")

        # Safety gate - check operation safety
        if not check_operation_safety(
            f"evaluate_modal_logic: {proposition}",
            {
                "operation_type": "modal_evaluation",
                "proposition": proposition,
                "parameters": kwargs
            }
        ):
            logger.error(f"Modal evaluation blocked by safety system: {proposition}")
            return {
                "result": "BLOCKED",
                "reason": "Safety violation - operation not permitted",
                "proposition": proposition,
                "safety_status": "BLOCKED"
            }

        logger.debug(f"Evaluating modal logic: {proposition}")
        return self._monitor.evaluate_modal_proposition(proposition, **kwargs)

    def evaluate_iel_logic(self, proposition: str, **kwargs) -> Dict[str, Any]:
        """
        Evaluate IEL proposition with full monitoring and safety gates

        Args:
            proposition: IEL formula to evaluate
            **kwargs: Additional evaluation parameters including identity/experience contexts

        Returns:
            Evaluation result with monitoring metadata
        """
        if not self._initialized:
            raise RuntimeError("LOGOS Core not initialized")

        # Safety gate - check operation safety
        if not check_operation_safety(
            f"evaluate_iel_logic: {proposition}",
            {
                "operation_type": "iel_evaluation",
                "proposition": proposition,
                "parameters": kwargs,
                "consequences": kwargs.get("consequences", {})
            }
        ):
            logger.error(f"IEL evaluation blocked by safety system: {proposition}")
            return {
                "result": "BLOCKED",
                "reason": "Safety violation - operation not permitted",
                "proposition": proposition,
                "safety_status": "BLOCKED"
            }

        logger.debug(f"Evaluating IEL logic: {proposition}")
        return self._monitor.evaluate_iel_proposition(proposition, **kwargs)

    def evaluate_batch(self, propositions: list, **kwargs) -> Dict[str, Any]:
        """
        Evaluate multiple propositions with monitoring and safety gates

        Args:
            propositions: List of propositions to evaluate
            **kwargs: Additional evaluation parameters

        Returns:
            Batch evaluation results with monitoring metadata
        """
        if not self._initialized:
            raise RuntimeError("LOGOS Core not initialized")

        # Safety gate - check batch operation safety
        if not check_operation_safety(
            f"evaluate_batch: {len(propositions)} propositions",
            {
                "operation_type": "batch_evaluation",
                "proposition_count": len(propositions),
                "propositions": propositions[:5],  # Sample for safety check
                "parameters": kwargs
            }
        ):
            logger.error(f"Batch evaluation blocked by safety system: {len(propositions)} propositions")
            return {
                "result": "BLOCKED",
                "reason": "Safety violation - batch operation not permitted",
                "proposition_count": len(propositions),
                "safety_status": "BLOCKED"
            }

        logger.debug(f"Evaluating batch of {len(propositions)} propositions")
        return self._monitor.evaluate_batch(propositions, **kwargs)

    def get_system_status(self) -> Dict[str, Any]:
        """
        Get comprehensive system status including safety framework

        Returns:
            System status including monitor state, safety status, and health metrics
        """
        if not self._initialized:
            return {"status": "not_initialized"}

        monitor_status = self._monitor.health_check()
        safety_status = self._safety_system.get_safety_status() if self._safety_system else {"status": "not_initialized"}
        iel_status = self._iel_integration.get_system_status() if self._iel_integration else {"iel_available": False}

        return {
            "logos_core": {
                "status": "operational" if self._initialized else "offline",
                "version": "2.0.0",
                "initialized": self._initialized
            },
            "reference_monitor": monitor_status,
            "integrity_safeguard": safety_status,
            "iel": iel_status,
            "capabilities": {
                "modal_logic": True,
                "iel_logic": True,
                "batch_processing": True,
                "anomaly_detection": True,
                "consistency_validation": True,
                "safety_gates": True,
                "emergency_halt": True
            }
        }

    def emergency_shutdown(self, reason: str = "Manual shutdown"):
        """
        Emergency shutdown with full state preservation and safety integration

        Args:
            reason: Reason for emergency shutdown
        """
        logger.critical(f"EMERGENCY SHUTDOWN: {reason}")

        # Trigger safety system emergency halt
        if self._safety_system:
            self._safety_system.emergency_trigger(f"Emergency shutdown: {reason}")

        if self._monitor:
            # Block all operations
            self._monitor.add_blocked_operation("*", f"Emergency shutdown: {reason}")
            self._monitor.emergency_halt = True

        self.shutdown()

    def clear_emergency_state(self, authorization_code: str):
        """
        Clear emergency state (requires authorization)

        Args:
            authorization_code: Authorization code for emergency override
        """
        if not self._initialized:
            return False

        self._monitor.clear_emergency_halt(authorization_code)
        return not self._monitor.emergency_halt

    def shutdown(self):
        """Clean shutdown of LOGOS Core system including safety framework"""
        if self._initialized:
            logger.info("Shutting down LOGOS Core system")

            # Shutdown safety system
            if self._safety_system:
                self._safety_system.stop_monitoring()

            # Reference monitor cleanup not needed
            self._initialized = False

# Global LOGOS Core instance
_global_core = None

def initialize_logos_core(config: Optional[Dict[str, Any]] = None) -> LOGOSCore:
    """
    Initialize global LOGOS Core instance

    Args:
        config: Optional configuration

    Returns:
        LOGOS Core instance
    """
    global _global_core
    if _global_core is None:
        _global_core = LOGOSCore(config)
    return _global_core

def get_logos_core() -> LOGOSCore:
    """
    Get global LOGOS Core instance (initialize if needed)

    Returns:
        LOGOS Core instance
    """
    global _global_core
    if _global_core is None:
        _global_core = LOGOSCore()
    return _global_core

def shutdown_logos_core():
    """Shutdown global LOGOS Core instance"""
    global _global_core
    if _global_core:
        _global_core.shutdown()
        _global_core = None

# Convenience functions for direct access
def evaluate_modal(proposition: str, **kwargs) -> Dict[str, Any]:
    """Convenience function for modal logic evaluation"""
    return get_logos_core().evaluate_modal_logic(proposition, **kwargs)

def evaluate_iel(proposition: str, **kwargs) -> Dict[str, Any]:
    """Convenience function for IEL evaluation"""
    return get_logos_core().evaluate_iel_logic(proposition, **kwargs)

def evaluate_batch(propositions: list, **kwargs) -> Dict[str, Any]:
    """Convenience function for batch evaluation"""
    return get_logos_core().evaluate_batch(propositions, **kwargs)

def get_status() -> Dict[str, Any]:
    """Convenience function for system status"""
    return get_logos_core().get_system_status()

# Module-level initialization for import-time setup
def _module_init():
    """Initialize module-level state"""
    # Create necessary directories
    logs_dir = Path("logs")
    logs_dir.mkdir(exist_ok=True)

    audit_dir = Path("audit")
    audit_dir.mkdir(exist_ok=True)

    # Set up basic logging if not already configured
    if not logging.getLogger().handlers:
        logging.basicConfig(
            level=logging.INFO,
            format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
        )

# Auto-initialize on import
_module_init()

if __name__ == "__main__":
    # Command-line interface for testing
    import argparse

    parser = argparse.ArgumentParser(description="LOGOS Core System")
    parser.add_argument('--test-modal', type=str, help="Test modal proposition")
    parser.add_argument('--test-iel', type=str, help="Test IEL proposition")
    parser.add_argument('--status', action='store_true', help="Show system status")
    parser.add_argument('--shutdown', action='store_true', help="Shutdown system")
    parser.add_argument('--emergency-halt', type=str, help="Trigger emergency halt with reason")

    args = parser.parse_args()

    core = initialize_logos_core()

    try:
        if args.status:
            status = core.get_system_status()
            print(json.dumps(status, indent=2))

        if args.test_modal:
            result = core.evaluate_modal_logic(args.test_modal)
            print(f"Modal result: {result}")

        if args.test_iel:
            result = core.evaluate_iel_logic(args.test_iel)
            print(f"IEL result: {result}")

        if args.shutdown:
            core.shutdown()

        if args.emergency_halt:
            core.emergency_shutdown(args.emergency_halt)

    except Exception as e:
        logger.error(f"Error: {e}")
        sys.exit(1)
