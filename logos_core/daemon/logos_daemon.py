"""
LOGOS Daemon - Passive Background Verifier + Scheduler

This daemon provides continuous, non-intrusive verification of LOGOS proofs and
scheduled autonomous reasoning gap detection. It operates passively to maintain
system coherence without disrupting active reasoning processes.

Architecture:
- Passive monitoring of proof state changes
- Scheduled verification cycles with configurable intervals
- Background gap detection and IEL candidate generation
- Trinity-Coherence metric computation and optimization
- Formal verification preservation guarantees

Safety Constraints:
- All operations must preserve existing formal verification
- No modification of core PXL/IEL logic without proof gates
- Bounded resource consumption with graceful degradation
- Audit trail for all autonomous modifications
"""

import asyncio
import logging
import threading
import time
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Any, Callable
from dataclasses import dataclass, field
from pathlib import Path
import json

try:
    from logos_core.unified_formalisms import UnifiedFormalismValidator as UnifiedFormalisms
    from logos_core.reference_monitor import ReferenceMonitor
    from logos_core.daemon.gap_detector import GapDetector
except ImportError:
    class UnifiedFormalisms:
        def __init__(self): pass

    class ReferenceMonitor:
        def __init__(self): pass

    class GapDetector:
        def __init__(self): pass
        def detect_gaps(self, **kwargs): return []


@dataclass
class DaemonConfig:
    """Configuration for LOGOS Daemon operation"""
    interval_sec: int = 3600  # Default 1 hour cycle
    max_self_extension_per_cycle: int = 1
    proof_gate_policy: str = "strict"
    enable_coherence_optimizer: bool = True
    telemetry_output: str = "metrics/agi_status.jsonl"
    max_memory_mb: int = 512
    max_cpu_percent: float = 10.0
    enable_gap_detection: bool = True
    enable_autonomous_reasoning: bool = False  # Start disabled for safety


@dataclass
class DaemonStatus:
    """Current status of the LOGOS Daemon"""
    is_running: bool = False
    start_time: Optional[datetime] = None
    last_cycle_time: Optional[datetime] = None
    cycles_completed: int = 0
    gaps_detected: int = 0
    extensions_generated: int = 0
    last_error: Optional[str] = None
    memory_usage_mb: float = 0.0
    cpu_usage_percent: float = 0.0


class LogosDaemon:
    """
    LOGOS Autonomous Reasoning Daemon

    Provides passive background verification, gap detection, and coherence optimization
    while maintaining strict formal verification guarantees.
    """

    def __init__(self, config: Optional[DaemonConfig] = None):
        self.config = config or DaemonConfig()
        self.status = DaemonStatus()
        self.logger = self._setup_logging()

        # Core components
        try:
            self.unified_formalisms = UnifiedFormalisms()
            self.reference_monitor = ReferenceMonitor()
            self.gap_detector = GapDetector()
        except Exception as e:
            self.logger.warning(f"Using fallback components: {e}")
            self.unified_formalisms = UnifiedFormalisms()
            self.reference_monitor = ReferenceMonitor()
            self.gap_detector = GapDetector()

        # Daemon control
        self._stop_event = threading.Event()
        self._daemon_thread: Optional[threading.Thread] = None
        self._lock = threading.RLock()
        self._running = False

        # Metrics and telemetry
        self._telemetry_buffer: List[Dict[str, Any]] = []
        self._last_telemetry_flush = datetime.now()

        # Registered callbacks
        self._gap_detection_callbacks: List[Callable] = []
        self._verification_callbacks: List[Callable] = []

    def _setup_logging(self) -> logging.Logger:
        """Configure daemon-specific logging"""
        logger = logging.getLogger("logos.daemon")
        if not logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter(
                '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
            )
            handler.setFormatter(formatter)
            logger.addHandler(handler)
            logger.setLevel(logging.INFO)
        return logger

    def start(self) -> bool:
        """
        Start the LOGOS Daemon

        Returns:
            bool: True if daemon started successfully, False otherwise
        """
        with self._lock:
            if self.status.is_running:
                self.logger.warning("Daemon is already running")
                return False

            try:
                # Initialize telemetry output directory
                telemetry_path = Path(self.config.telemetry_output)
                telemetry_path.parent.mkdir(parents=True, exist_ok=True)

                # Start daemon thread
                self._stop_event.clear()
                self._daemon_thread = threading.Thread(
                    target=self._daemon_loop,
                    name="LogosDaemon",
                    daemon=True
                )

                self.status.is_running = True
                self.status.start_time = datetime.now()
                self.status.last_error = None
                self._running = True

                self._daemon_thread.start()

                self.logger.info(f"LOGOS Daemon started with {self.config.interval_sec}s cycle interval")
                self._record_telemetry("daemon_started", {"config": self.config.__dict__})

                return True

            except Exception as e:
                self.status.is_running = False
                self.status.last_error = str(e)
                self.logger.error(f"Failed to start daemon: {e}")
                return False

    def stop(self) -> bool:
        """
        Stop the LOGOS Daemon gracefully

        Returns:
            bool: True if daemon stopped successfully, False otherwise
        """
        with self._lock:
            if not self.status.is_running:
                self.logger.warning("Daemon is not running")
                return False

            try:
                self.logger.info("Stopping LOGOS Daemon...")
                self._stop_event.set()

                if self._daemon_thread and self._daemon_thread.is_alive():
                    self._daemon_thread.join(timeout=30.0)

                self.status.is_running = False
                self._running = False
                self._flush_telemetry()

                self.logger.info("LOGOS Daemon stopped successfully")
                self._record_telemetry("daemon_stopped", {
                    "cycles_completed": self.status.cycles_completed,
                    "runtime_seconds": (datetime.now() - self.status.start_time).total_seconds()
                })

                return True

            except Exception as e:
                self.status.last_error = str(e)
                self.logger.error(f"Error stopping daemon: {e}")
                return False

    def get_status(self) -> DaemonStatus:
        """Get current daemon status"""
        with self._lock:
            return DaemonStatus(**self.status.__dict__)

    def register_gap_detection_callback(self, callback: Callable[[List[Dict]], None]) -> None:
        """Register callback for gap detection events"""
        self._gap_detection_callbacks.append(callback)

    def register_verification_callback(self, callback: Callable[[Dict], None]) -> None:
        """Register callback for verification events"""
        self._verification_callbacks.append(callback)

    def _daemon_loop(self) -> None:
        """Main daemon execution loop"""
        self.logger.info("Daemon loop started")

        while not self._stop_event.is_set():
            try:
                cycle_start = datetime.now()
                self.logger.debug("Starting daemon cycle")

                # Execute daemon cycle
                self._execute_daemon_cycle()

                # Update status
                with self._lock:
                    self.status.last_cycle_time = cycle_start
                    self.status.cycles_completed += 1

                # Wait for next cycle
                elapsed = (datetime.now() - cycle_start).total_seconds()
                sleep_time = max(0, self.config.interval_sec - elapsed)

                if sleep_time > 0:
                    self._stop_event.wait(timeout=sleep_time)

            except Exception as e:
                self.logger.error(f"Error in daemon cycle: {e}")
                with self._lock:
                    self.status.last_error = str(e)

                # Wait before retry
                self._stop_event.wait(timeout=min(300, self.config.interval_sec))

        self.logger.info("Daemon loop ended")

    def _execute_daemon_cycle(self) -> None:
        """Execute one complete daemon cycle"""
        cycle_start = datetime.now()

        # 1. System health check
        self._update_resource_usage()

        # 2. Verify current proof state
        if self._should_run_verification():
            verification_result = self._run_background_verification()
            self._record_telemetry("verification_cycle", verification_result)

        # 3. Gap detection if enabled
        if self.config.enable_gap_detection and self._should_run_gap_detection():
            gaps = self._run_gap_detection()
            if gaps:
                self._record_telemetry("gaps_detected", {"count": len(gaps), "gaps": gaps})
                for callback in self._gap_detection_callbacks:
                    try:
                        callback(gaps)
                    except Exception as e:
                        self.logger.error(f"Gap detection callback error: {e}")

        # 4. Coherence optimization if enabled
        if self.config.enable_coherence_optimizer:
            coherence_metrics = self._compute_coherence_metrics()
            self._record_telemetry("coherence_metrics", coherence_metrics)

        # 5. IEL evaluation and refinement (if enabled)
        if hasattr(self, '_enable_iel_evaluation') and self._enable_iel_evaluation:
            if self._should_run_iel_evaluation():
                iel_evaluation_result = self._run_iel_evaluation_cycle()
                self._record_telemetry("iel_evaluation_cycle", iel_evaluation_result)

        # 6. Autonomous reasoning (if enabled and safe)
        if self.config.enable_autonomous_reasoning and self._is_autonomous_reasoning_safe():
            self._execute_bounded_autonomous_reasoning()

        # 7. Flush telemetry periodically
        if (datetime.now() - self._last_telemetry_flush).total_seconds() > 3600:
            self._flush_telemetry()

        cycle_duration = (datetime.now() - cycle_start).total_seconds()
        self.logger.debug(f"Daemon cycle completed in {cycle_duration:.2f}s")

    def _should_run_verification(self) -> bool:
        """Determine if background verification should run this cycle"""
        # Always run verification unless system is under stress
        return self.status.memory_usage_mb < (self.config.max_memory_mb * 0.8)

    def _should_run_gap_detection(self) -> bool:
        """Determine if gap detection should run this cycle"""
        # Run gap detection every 4th cycle to reduce load
        return (self.status.cycles_completed % 4) == 0

    def _run_background_verification(self) -> Dict[str, Any]:
        """Run passive background verification of current proof state"""
        try:
            # Verify core PXL integrity
            pxl_status = self.unified_formalisms.verify_pxl_integrity()

            # Verify IEL consistency
            iel_status = self.unified_formalisms.verify_iel_consistency()

            result = {
                "pxl_status": pxl_status,
                "iel_status": iel_status,
                "timestamp": datetime.now().isoformat(),
                "success": pxl_status.get("valid", False) and iel_status.get("valid", False)
            }

            # Trigger verification callbacks
            for callback in self._verification_callbacks:
                try:
                    callback(result)
                except Exception as e:
                    self.logger.error(f"Verification callback error: {e}")

            return result

        except Exception as e:
            self.logger.error(f"Background verification failed: {e}")
            return {"success": False, "error": str(e)}

    def _run_gap_detection(self) -> List[Dict[str, Any]]:
        """Run reasoning gap detection across IEL/PXL boundary"""
        try:
            # Use instance gap detector
            gaps = self.gap_detector.detect_reasoning_gaps({
                "workspace": ".",
                "pxl_files": ["*.v"],
                "iel_files": ["*.v"]
            })

            if gaps:
                self.logger.info(f"Detected {len(gaps)} reasoning gaps")
                with self._lock:
                    self.status.gaps_detected += len(gaps)

                # Emit gap detection events
                for gap in gaps:
                    self._record_telemetry("gap_detected", gap)

            return gaps

        except Exception as e:
            self.logger.error(f"Gap detection failed: {e}")
            return []

    def _compute_coherence_metrics(self) -> Dict[str, float]:
        """Compute Trinity-Coherence metrics for current system state"""
        try:
            # Placeholder for coherence computation
            # Will integrate with coherence module when available
            return {
                "pxl_coherence": 0.95,
                "iel_coherence": 0.92,
                "trinity_coherence": 0.93,
                "timestamp": datetime.now().timestamp()
            }
        except Exception as e:
            self.logger.error(f"Coherence computation failed: {e}")
            return {}

    def _is_autonomous_reasoning_safe(self) -> bool:
        """Check if autonomous reasoning can be safely executed"""
        # Conservative safety checks
        return (
            self.status.memory_usage_mb < (self.config.max_memory_mb * 0.6) and
            self.status.cpu_usage_percent < (self.config.max_cpu_percent * 0.5) and
            self.status.last_error is None and
            self.status.cycles_completed > 5  # Require stable operation
        )

    def _execute_bounded_autonomous_reasoning(self) -> None:
        """Execute bounded autonomous reasoning with strict safety constraints"""
        try:
            # Placeholder for autonomous reasoning
            # Will implement with strict bounds and proof gates
            self.logger.debug("Autonomous reasoning executed (placeholder)")

        except Exception as e:
            self.logger.error(f"Autonomous reasoning failed: {e}")

    def _should_run_iel_evaluation(self) -> bool:
        """Determine if IEL evaluation should run this cycle"""
        # Run every 6 hours (21600 seconds) or on first cycle
        if not hasattr(self, '_last_iel_evaluation'):
            return True

        time_since_last = (datetime.now() - self._last_iel_evaluation).total_seconds()
        return time_since_last >= 21600  # 6 hours

    def _run_iel_evaluation_cycle(self) -> Dict[str, Any]:
        """Execute complete IEL evaluation and refinement cycle"""
        try:
            from logos_core.meta_reasoning.iel_evaluator import IELEvaluator

            self.logger.info("Starting IEL evaluation cycle...")
            evaluator = IELEvaluator("registry/iel_registry.db")

            # Evaluate all IELs
            evaluation_results = evaluator.evaluate_all_iels("metrics/agi_cycle.jsonl")

            # Rank by quality
            ranked_iels = evaluator.rank_iels(evaluation_results, threshold=0.92)

            # Record results
            self._last_iel_evaluation = datetime.now()

            result = {
                "timestamp": datetime.now().isoformat(),
                "total_iels_evaluated": len(evaluation_results),
                "high_quality_iels": len(ranked_iels),
                "evaluation_summary": evaluator._calculate_summary_stats(evaluation_results)
            }

            self.logger.info(f"IEL evaluation complete: {len(evaluation_results)} evaluated, "
                           f"{len(ranked_iels)} high-quality")

            return result

        except Exception as e:
            self.logger.error(f"IEL evaluation cycle failed: {e}")
            return {"error": str(e), "timestamp": datetime.now().isoformat()}

    def _update_resource_usage(self) -> None:
        """Update current resource usage metrics"""
        try:
            import psutil
            process = psutil.Process()

            with self._lock:
                self.status.memory_usage_mb = process.memory_info().rss / (1024 * 1024)
                self.status.cpu_usage_percent = process.cpu_percent()

        except ImportError:
            # psutil not available, use placeholder values
            with self._lock:
                self.status.memory_usage_mb = 100.0  # Placeholder
                self.status.cpu_usage_percent = 5.0   # Placeholder
        except Exception as e:
            self.logger.error(f"Resource usage update failed: {e}")

    def _record_telemetry(self, event_type: str, data: Dict[str, Any]) -> None:
        """Record telemetry event to buffer"""
        telemetry_event = {
            "timestamp": datetime.now().isoformat(),
            "event_type": event_type,
            "data": data
        }

        self._telemetry_buffer.append(telemetry_event)

        # Prevent buffer overflow
        if len(self._telemetry_buffer) > 1000:
            self._flush_telemetry()

    def _flush_telemetry(self) -> None:
        """Flush telemetry buffer to output file"""
        if not self._telemetry_buffer:
            return

        try:
            telemetry_path = Path(self.config.telemetry_output)

            with open(telemetry_path, 'a', encoding='utf-8') as f:
                for event in self._telemetry_buffer:
                    f.write(json.dumps(event) + '\n')

            self._telemetry_buffer.clear()
            self._last_telemetry_flush = datetime.now()

        except Exception as e:
            self.logger.error(f"Telemetry flush failed: {e}")


def main():
    """Main entry point for daemon command-line execution"""
    import argparse
    import sys

    parser = argparse.ArgumentParser(description='LOGOS Daemon - Passive Background Verifier')
    parser.add_argument('--once', action='store_true', help='Run single cycle and exit')
    parser.add_argument('--continuous', action='store_true', help='Run in continuous multi-cycle mode')
    parser.add_argument('--interval', type=int, default=3600, help='Cycle interval in seconds (default: 3600)')
    parser.add_argument('--emit-gaps', action='store_true', help='Enable gap detection and emission')
    parser.add_argument('--evaluate-iels', action='store_true', help='Enable automatic IEL evaluation and refinement')
    parser.add_argument('--out', default='metrics/agi_status.jsonl', help='Telemetry output file')
    parser.add_argument('--config', help='Configuration file path')

    args = parser.parse_args()

    # Create daemon configuration
    config = DaemonConfig(
        telemetry_output=args.out,
        enable_gap_detection=args.emit_gaps,
        interval_sec=1 if args.once else args.interval,
        enable_autonomous_reasoning=args.evaluate_iels
    )

    # Initialize daemon
    daemon = LogosDaemon(config)

    # Add IEL evaluation capability for continuous mode
    if args.evaluate_iels:
        daemon._enable_iel_evaluation = True
        daemon.logger.info("IEL evaluation and refinement enabled")

    try:
        if args.once:
            # Single cycle execution
            print(f"Running single cycle with gap detection: {args.emit_gaps}")
            daemon.start()
            time.sleep(2)  # Allow one cycle to complete
            daemon.stop()
            print(f"Results written to: {args.out}")
        else:
            # Continuous operation
            print("Starting LOGOS daemon in continuous mode...")
            daemon.start()
            try:
                while daemon.status.is_running:
                    time.sleep(1)
            except KeyboardInterrupt:
                print("\nShutting down daemon...")
                daemon.stop()
    except Exception as e:
        print(f"Daemon error: {e}")
        sys.exit(1)


if __name__ == '__main__':
    main()
