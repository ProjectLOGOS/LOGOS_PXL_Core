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

from enhanced_reference_monitor import get_global_monitor, shutdown_monitor
from runtime.iel_runtime_interface import ModalLogicEvaluator, IELEvaluator
from eschaton_safety import get_global_safety_system, check_operation_safety, emergency_halt

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

        # Register cleanup
        atexit.register(self.shutdown)

        logger.info("LOGOS Core system initialized with safety framework")

    def _setup_logging(self):
        """Setup system logging"""
        log_level = self.config.get('log_level', 'INFO')
        logging.basicConfig(
            level=getattr(logging, log_level),
            format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
        )

    def _initialize_monitor(self):
        """Initialize the enhanced reference monitor"""
        try:
            self._monitor = get_global_monitor()
            self._initialized = True
            logger.info("Enhanced Reference Monitor integration successful")
        except Exception as e:
            logger.error(f"Failed to initialize reference monitor: {e}")
            raise

    def _initialize_safety_system(self):
        """Initialize the eschatological safety system"""
        try:
            self._safety_system = get_global_safety_system()

            # Add violation handler to integrate with monitor
            self._safety_system.add_violation_handler(self._handle_safety_violation)

            logger.info("Eschatological Safety System integration successful")
        except Exception as e:
            logger.error(f"Failed to initialize safety system: {e}")
            raise

    def _handle_safety_violation(self, violation):
        """Handle safety violations from the safety system"""
        logger.critical(f"SAFETY VIOLATION: {violation.safeguard_state.name} - {violation.metadata.get('reason', 'Unknown')}")

        # Block all operations in reference monitor
        if self._monitor:
            self._monitor.add_blocked_operation("*", f"Safety violation: {violation.safeguard_state.name}")

        # If irreversible, trigger emergency halt
        if not violation.reversible:
            logger.critical("IRREVERSIBLE VIOLATION - TRIGGERING EMERGENCY HALT")
            if self._monitor:
                self._monitor.emergency_halt = True

    @property
    def monitor(self):
        """Access to the reference monitor"""
        if not self._initialized:
            raise RuntimeError("LOGOS Core not initialized")
        return self._monitor

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

        monitor_status = self._monitor.get_monitor_status()
        safety_status = self._safety_system.get_safety_status() if self._safety_system else {"status": "not_initialized"}

        return {
            "logos_core": {
                "status": "operational" if self._initialized else "offline",
                "version": "2.0.0",
                "initialized": self._initialized
            },
            "reference_monitor": monitor_status,
            "eschatological_safety": safety_status,
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
            self._safety_system.eschaton_trigger(f"Emergency shutdown: {reason}")

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

            # Shutdown reference monitor
            shutdown_monitor()
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
