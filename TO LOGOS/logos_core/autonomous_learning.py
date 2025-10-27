"""
Autonomous Learning Framework - Self-Improvement Engine

This module implements a comprehensive autonomous learning system that:
1. Analyzes reasoning gaps from telemetry data
2. Generates IEL candidate solutions
3. Evaluates and validates candidates
4. Integrates successful ones into the registry

The system operates with formal safety constraints to ensure all learned
behaviors maintain logical consistency and system integrity.
"""

import json
import logging
import time
import uuid
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Set, Optional, Any, Tuple
from dataclasses import dataclass, field
from collections import defaultdict, Counter
import threading
import sqlite3

# Core imports
from logos_core.meta_reasoning.iel_generator import IELGenerator, IELCandidate, GenerationConfig
from logos_core.meta_reasoning.iel_evaluator import IELEvaluator
from logos_core.meta_reasoning.iel_registry import IELRegistry, IELRegistryEntry
from logos_core.enhanced_reference_monitor import get_global_monitor

logger = logging.getLogger(__name__)

@dataclass
class ReasoningGap:
    """Represents an identified reasoning gap from telemetry analysis"""
    gap_id: str
    gap_type: str  # "evaluation_failure", "consistency_violation", "performance_anomaly"
    domain: str
    description: str
    severity: float  # 0.0 to 1.0
    frequency: int
    propositions: List[str]
    error_patterns: List[str]
    context_data: Dict[str, Any]
    first_seen: datetime
    last_seen: datetime

    def to_dict(self) -> Dict[str, Any]:
        return {
            "gap_id": self.gap_id,
            "gap_type": self.gap_type,
            "domain": self.domain,
            "description": self.description,
            "severity": self.severity,
            "frequency": self.frequency,
            "propositions": self.propositions,
            "error_patterns": self.error_patterns,
            "context_data": self.context_data,
            "first_seen": self.first_seen.isoformat(),
            "last_seen": self.last_seen.isoformat()
        }

@dataclass
class LearningConfig:
    """Configuration for autonomous learning cycle"""
    max_candidates_per_gap: int = 5
    evaluation_threshold: float = 0.7
    min_gap_frequency: int = 3
    min_gap_severity: float = 0.3
    learning_history_days: int = 7
    max_learning_cycles_per_hour: int = 2
    enable_cross_domain_learning: bool = True
    enable_conservative_mode: bool = True
    registry_path: str = "registry/iel_registry.db"

class TelemetryAnalyzer:
    """Analyzes telemetry data to identify reasoning gaps"""

    def __init__(self, telemetry_file: str):
        self.telemetry_file = Path(telemetry_file)

    def load_telemetry(self, since: Optional[datetime] = None) -> List[Dict[str, Any]]:
        """Load telemetry records since specified time"""
        if not self.telemetry_file.exists():
            logger.warning(f"Telemetry file not found: {self.telemetry_file}")
            return []

        records = []
        cutoff_time = since or (datetime.now() - timedelta(days=7))
        # Ensure timezone-naive comparison
        if cutoff_time.tzinfo is not None:
            cutoff_time = cutoff_time.replace(tzinfo=None)

        try:
            with open(self.telemetry_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        record = json.loads(line)
                        # Parse timestamp
                        timestamp_str = record.get('timestamp', '')
                        if timestamp_str:
                            # Handle timezone properly
                            if timestamp_str.endswith('Z'):
                                timestamp_str = timestamp_str[:-1]  # Remove Z for naive parsing
                            record_time = datetime.fromisoformat(timestamp_str)
                            if record_time.tzinfo is not None:
                                record_time = record_time.replace(tzinfo=None)

                            if record_time >= cutoff_time:
                                records.append(record)
                        else:
                            # Include records without timestamps
                            records.append(record)
                    except (json.JSONDecodeError, ValueError) as e:
                        logger.warning(f"Failed to parse telemetry line: {e}")

        except Exception as e:
            logger.error(f"Error reading telemetry file: {e}")

        return records

    def identify_reasoning_gaps(self, records: List[Dict[str, Any]],
                              config: LearningConfig) -> List[ReasoningGap]:
        """Identify reasoning gaps from telemetry records"""
        gaps = []

        # Group failures by error pattern and proposition type
        failure_patterns = defaultdict(list)
        error_frequencies = Counter()

        for record in records:
            eval_record = record.get('evaluation_record', {})
            if not eval_record.get('success', True):
                error_msg = eval_record.get('error_message', 'Unknown error')
                proposition = eval_record.get('input_data', {}).get('proposition', '')
                evaluator_type = eval_record.get('evaluator_type', 'unknown')

                # Categorize the failure
                pattern_key = self._extract_error_pattern(error_msg, proposition, evaluator_type)
                failure_patterns[pattern_key].append(eval_record)
                error_frequencies[pattern_key] += 1

        # Convert patterns to reasoning gaps
        for pattern, failures in failure_patterns.items():
            if len(failures) >= config.min_gap_frequency:
                gap = self._create_reasoning_gap(pattern, failures, config)
                if gap.severity >= config.min_gap_severity:
                    gaps.append(gap)

        return gaps

    def _extract_error_pattern(self, error_msg: str, proposition: str,
                              evaluator_type: str) -> str:
        """Extract error pattern for grouping similar failures"""
        # Categorize by error type
        if "file specified" in error_msg.lower():
            return f"bridge_unavailable_{evaluator_type}"
        elif "validation failed" in error_msg.lower():
            return f"validation_failure_{evaluator_type}"
        elif "timeout" in error_msg.lower():
            return f"timeout_{evaluator_type}"
        elif "syntax" in error_msg.lower():
            return f"syntax_error_{evaluator_type}"
        elif "consistency" in error_msg.lower():
            return f"consistency_violation_{evaluator_type}"
        else:
            # Generalize by proposition complexity
            if len(proposition) > 100:
                return f"complex_proposition_{evaluator_type}"
            elif "[]" in proposition or "<>" in proposition:
                return f"modal_logic_{evaluator_type}"
            elif "I(" in proposition or "E(" in proposition:
                return f"iel_logic_{evaluator_type}"
            else:
                return f"propositional_logic_{evaluator_type}"

    def _create_reasoning_gap(self, pattern: str, failures: List[Dict[str, Any]],
                            config: LearningConfig) -> ReasoningGap:
        """Create a ReasoningGap from failure pattern"""

        # Extract common characteristics
        propositions = [f.get('input_data', {}).get('proposition', '') for f in failures]
        unique_props = list(set(p for p in propositions if p))

        error_messages = [f.get('error_message', '') for f in failures]
        unique_errors = list(set(e for e in error_messages if e))

        # Determine domain
        if "modal" in pattern:
            domain = "modal_logic"
        elif "iel" in pattern:
            domain = "iel_logic"
        elif "bridge" in pattern:
            domain = "bridge_infrastructure"
        elif "validation" in pattern:
            domain = "input_validation"
        else:
            domain = "general_reasoning"

        # Calculate severity based on frequency and impact
        frequency = len(failures)
        severity = min(1.0, frequency / 10.0)  # Cap at 1.0, scale by frequency

        # Extract timestamps
        timestamps = []
        for f in failures:
            try:
                timestamps.append(datetime.fromtimestamp(f.get('timestamp', 0)))
            except (ValueError, TypeError):
                pass

        first_seen = min(timestamps) if timestamps else datetime.now()
        last_seen = max(timestamps) if timestamps else datetime.now()

        # Generate description
        description = self._generate_gap_description(pattern, frequency, unique_props[:3])

        return ReasoningGap(
            gap_id=str(uuid.uuid4()),
            gap_type="evaluation_failure",
            domain=domain,
            description=description,
            severity=severity,
            frequency=frequency,
            propositions=unique_props[:10],  # Limit to first 10
            error_patterns=unique_errors[:5],  # Limit to first 5
            context_data={"pattern": pattern, "sample_failures": failures[:3]},
            first_seen=first_seen,
            last_seen=last_seen
        )

    def _generate_gap_description(self, pattern: str, frequency: int,
                                sample_props: List[str]) -> str:
        """Generate human-readable description of the gap"""
        if "bridge_unavailable" in pattern:
            return f"Bridge infrastructure unavailable ({frequency} failures). Need fallback evaluation strategies."
        elif "validation_failure" in pattern:
            return f"Input validation failures ({frequency} occurrences). Need enhanced validation rules."
        elif "modal_logic" in pattern:
            return f"Modal logic evaluation issues ({frequency} failures). Need improved modal operators."
        elif "iel_logic" in pattern:
            return f"IEL evaluation challenges ({frequency} failures). Need enhanced identity/experience operators."
        elif "complex_proposition" in pattern:
            return f"Complex proposition handling ({frequency} failures). Need decomposition strategies."
        else:
            return f"General reasoning gaps ({frequency} failures) in pattern: {pattern}"

class LearningCycleManager:
    """Manages the complete autonomous learning cycle"""

    def __init__(self, config: Optional[LearningConfig] = None):
        self.config = config or LearningConfig()
        self.analyzer = TelemetryAnalyzer("logs/monitor_telemetry.jsonl")
        self.generator = IELGenerator()
        self.evaluator = IELEvaluator()
        self.registry = IELRegistry(self.config.registry_path)

        # Learning state tracking
        self.learning_history = []
        self.last_cycle_time = None
        self.cycle_count = 0

        # Thread safety
        self._lock = threading.Lock()

        logger.info("Autonomous Learning Framework initialized")

    def run_learning_cycle(self) -> Dict[str, Any]:
        """Execute a complete learning cycle"""
        cycle_start = datetime.now()
        cycle_id = str(uuid.uuid4())

        logger.info(f"Starting learning cycle {cycle_id}")

        try:
            # Check rate limiting
            if not self._check_rate_limit():
                return {
                    "cycle_id": cycle_id,
                    "status": "rate_limited",
                    "message": "Rate limit exceeded for learning cycles"
                }

            # Step 1: Analyze telemetry for reasoning gaps
            since_time = datetime.now() - timedelta(days=self.config.learning_history_days)
            telemetry_records = self.analyzer.load_telemetry(since=since_time)

            logger.info(f"Loaded {len(telemetry_records)} telemetry records")

            gaps = self.analyzer.identify_reasoning_gaps(telemetry_records, self.config)
            logger.info(f"Identified {len(gaps)} reasoning gaps")

            if not gaps:
                return {
                    "cycle_id": cycle_id,
                    "status": "no_gaps",
                    "message": "No significant reasoning gaps found"
                }

            # Step 2: Generate IEL candidates for each gap
            all_candidates = []
            for gap in gaps:
                candidates = self._generate_candidates_for_gap(gap)
                all_candidates.extend(candidates)
                logger.info(f"Generated {len(candidates)} candidates for gap: {gap.description}")

            # Step 3: Evaluate candidates
            evaluation_results = []
            accepted_candidates = []
            rejected_candidates = []

            for candidate in all_candidates:
                try:
                    result = self.evaluator.evaluate_candidate(candidate)
                    evaluation_results.append(result)

                    if result.get('overall_score', 0) >= self.config.evaluation_threshold:
                        accepted_candidates.append((candidate, result))
                        logger.info(f"Accepted candidate: {candidate.rule_name} (score: {result.get('overall_score', 0):.3f})")
                    else:
                        rejected_candidates.append((candidate, result))
                        logger.debug(f"Rejected candidate: {candidate.rule_name} (score: {result.get('overall_score', 0):.3f})")

                except Exception as e:
                    logger.error(f"Error evaluating candidate {candidate.id}: {e}")
                    rejected_candidates.append((candidate, {"error": str(e)}))

            # Step 4: Store accepted candidates in registry
            registered_count = 0
            for candidate, eval_result in accepted_candidates:
                try:
                    if self._register_candidate(candidate, eval_result):
                        registered_count += 1
                except Exception as e:
                    logger.error(f"Error registering candidate {candidate.id}: {e}")

            # Step 5: Log learning cycle results
            cycle_result = {
                "cycle_id": cycle_id,
                "status": "completed",
                "start_time": cycle_start.isoformat(),
                "end_time": datetime.now().isoformat(),
                "gaps_identified": len(gaps),
                "candidates_generated": len(all_candidates),
                "candidates_accepted": len(accepted_candidates),
                "candidates_rejected": len(rejected_candidates),
                "candidates_registered": registered_count,
                "gaps": [gap.to_dict() for gap in gaps],
                "evaluation_summary": {
                    "total_evaluations": len(evaluation_results),
                    "acceptance_rate": len(accepted_candidates) / len(all_candidates) if all_candidates else 0,
                    "average_accepted_score": sum(r.get('overall_score', 0) for _, r in accepted_candidates) / len(accepted_candidates) if accepted_candidates else 0
                }
            }

            self._record_cycle_result(cycle_result)

            logger.info(f"Learning cycle {cycle_id} completed: {registered_count} new IELs registered")
            return cycle_result

        except Exception as e:
            logger.error(f"Learning cycle {cycle_id} failed: {e}")
            return {
                "cycle_id": cycle_id,
                "status": "failed",
                "error": str(e),
                "start_time": cycle_start.isoformat(),
                "end_time": datetime.now().isoformat()
            }

    def _check_rate_limit(self) -> bool:
        """Check if learning cycle rate limit is exceeded"""
        with self._lock:
            current_time = datetime.now()

            # Count cycles in the last hour
            hour_ago = current_time - timedelta(hours=1)
            recent_cycles = [
                cycle for cycle in self.learning_history[-20:]  # Check last 20 cycles
                if datetime.fromisoformat(cycle.get('start_time', '1970-01-01')) >= hour_ago
            ]

            if len(recent_cycles) >= self.config.max_learning_cycles_per_hour:
                logger.warning(f"Rate limit exceeded: {len(recent_cycles)} cycles in last hour")
                return False

            return True

    def _generate_candidates_for_gap(self, gap: ReasoningGap) -> List[IELCandidate]:
        """Generate IEL candidates to address a specific gap"""
        try:
            # Configure generation based on gap characteristics
            gen_config = GenerationConfig(
                max_candidates_per_gap=self.config.max_candidates_per_gap,
                min_confidence_threshold=0.4,
                enable_domain_bridging=self.config.enable_cross_domain_learning
            )

            # Convert ReasoningGap to format expected by generator
            gap_data = {
                "gap_type": gap.gap_type,
                "domain": gap.domain,
                "description": gap.description,
                "severity": gap.severity,
                "required_premises": gap.propositions[:3],  # Use sample propositions
                "expected_conclusion": f"resolve_{gap.domain}_gap",
                "confidence": min(0.8, gap.severity + 0.2)
            }

            candidates = self.generator.generate_candidates_for_gap(gap_data, gen_config)

            # Add metadata about the source gap
            for candidate in candidates:
                candidate.metadata = getattr(candidate, 'metadata', {})
                candidate.metadata.update({
                    "source_gap_id": gap.gap_id,
                    "gap_frequency": gap.frequency,
                    "gap_severity": gap.severity
                })

            return candidates

        except Exception as e:
            logger.error(f"Error generating candidates for gap {gap.gap_id}: {e}")
            return []

    def _register_candidate(self, candidate: IELCandidate, eval_result: Dict[str, Any]) -> bool:
        """Register an accepted candidate in the IEL registry"""
        try:
            # Create registry entry
            entry = IELRegistryEntry(
                id=candidate.id,
                domain=candidate.domain,
                rule_name=candidate.rule_name,
                rule_content=candidate.rule_template,
                content_hash=candidate.hash,
                version=1,
                status="pending",  # Will be verified before activation
                created_at=datetime.now(),
                metadata={
                    "evaluation_score": eval_result.get('overall_score', 0),
                    "confidence": candidate.confidence,
                    "source": "autonomous_learning",
                    "evaluation_details": eval_result
                }
            )

            # Store in registry
            success = self.registry.register_iel(entry)

            if success:
                logger.info(f"Registered IEL candidate: {candidate.rule_name}")
                return True
            else:
                logger.warning(f"Failed to register IEL candidate: {candidate.rule_name}")
                return False

        except Exception as e:
            logger.error(f"Error registering candidate {candidate.id}: {e}")
            return False

    def _record_cycle_result(self, result: Dict[str, Any]):
        """Record learning cycle result for history tracking"""
        with self._lock:
            self.learning_history.append(result)
            # Keep only last 100 cycles
            if len(self.learning_history) > 100:
                self.learning_history = self.learning_history[-100:]

            self.last_cycle_time = datetime.now()
            self.cycle_count += 1

            # Persist to file
            try:
                history_file = Path("logs/learning_history.jsonl")
                history_file.parent.mkdir(exist_ok=True)

                with open(history_file, 'a') as f:
                    f.write(json.dumps(result) + '\n')

            except Exception as e:
                logger.error(f"Error persisting learning history: {e}")

    def get_learning_status(self) -> Dict[str, Any]:
        """Get current learning system status"""
        with self._lock:
            return {
                "total_cycles": self.cycle_count,
                "last_cycle": self.last_cycle_time.isoformat() if self.last_cycle_time else None,
                "recent_cycles": len([
                    c for c in self.learning_history[-10:]
                    if datetime.fromisoformat(c.get('start_time', '1970-01-01')) >=
                       datetime.now() - timedelta(hours=24)
                ]),
                "total_gaps_identified": sum(c.get('gaps_identified', 0) for c in self.learning_history),
                "total_candidates_generated": sum(c.get('candidates_generated', 0) for c in self.learning_history),
                "total_candidates_registered": sum(c.get('candidates_registered', 0) for c in self.learning_history),
                "average_acceptance_rate": sum(c.get('evaluation_summary', {}).get('acceptance_rate', 0) for c in self.learning_history) / len(self.learning_history) if self.learning_history else 0,
                "config": {
                    "max_candidates_per_gap": self.config.max_candidates_per_gap,
                    "evaluation_threshold": self.config.evaluation_threshold,
                    "learning_history_days": self.config.learning_history_days,
                    "max_cycles_per_hour": self.config.max_learning_cycles_per_hour
                }
            }

# Global learning manager instance
_global_learning_manager = None

def get_global_learning_manager() -> LearningCycleManager:
    """Get or create global learning manager instance"""
    global _global_learning_manager
    if _global_learning_manager is None:
        _global_learning_manager = LearningCycleManager()
    return _global_learning_manager

def shutdown_learning_manager():
    """Shutdown global learning manager"""
    global _global_learning_manager
    if _global_learning_manager:
        logger.info("Shutting down Autonomous Learning Framework")
        _global_learning_manager = None
