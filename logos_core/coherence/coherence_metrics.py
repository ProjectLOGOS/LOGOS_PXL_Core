"""
Coherence Metrics - Trinity-Coherence Computation Model

Computes Trinity-Coherence metrics for LOGOS AGI system state, measuring the
coherence between PXL formal layer, IEL inference layer, and runtime behavior.
Provides quantitative measures for autonomous system optimization.

Architecture:
- PXL Coherence: Formal verification completeness and consistency
- IEL Coherence: Inference rule coverage and logical consistency  
- Runtime Coherence: Operational behavior alignment with formal specifications
- Trinity-Coherence: Unified metric combining all three dimensions
- Temporal coherence tracking with trend analysis

Mathematical Model:
Trinity-Coherence = α·PXL_Coherence + β·IEL_Coherence + γ·Runtime_Coherence
where α + β + γ = 1 and weights are dynamically adjusted based on system state.

Safety Constraints:
- All computations must be bounded and terminable
- Metric computation must not modify system state
- Emergency degradation detection with alerting
- Historical coherence preservation for rollback
"""

import logging
import math
import statistics
from typing import Dict, List, Set, Optional, Any, Tuple, NamedTuple
from dataclasses import dataclass, field
from datetime import datetime, timedelta
from collections import defaultdict, deque
import json

from ..unified_formalisms import UnifiedFormalisms


class CoherenceVector(NamedTuple):
    """Represents coherence in three dimensions"""
    pxl_coherence: float
    iel_coherence: float
    runtime_coherence: float
    
    @property
    def trinity_coherence(self) -> float:
        """Compute Trinity-Coherence with equal weighting"""
        return (self.pxl_coherence + self.iel_coherence + self.runtime_coherence) / 3.0
        
    def weighted_trinity_coherence(self, weights: Tuple[float, float, float]) -> float:
        """Compute Trinity-Coherence with custom weights"""
        α, β, γ = weights
        return α * self.pxl_coherence + β * self.iel_coherence + γ * self.runtime_coherence


@dataclass
class CoherenceSnapshot:
    """Snapshot of system coherence at a point in time"""
    timestamp: datetime
    coherence_vector: CoherenceVector
    trinity_coherence: float
    metadata: Dict[str, Any] = field(default_factory=dict)
    
    def to_dict(self) -> Dict[str, Any]:
        """Convert to dictionary for serialization"""
        return {
            "timestamp": self.timestamp.isoformat(),
            "pxl_coherence": self.coherence_vector.pxl_coherence,
            "iel_coherence": self.coherence_vector.iel_coherence,
            "runtime_coherence": self.coherence_vector.runtime_coherence,
            "trinity_coherence": self.trinity_coherence,
            "metadata": self.metadata
        }


@dataclass
class CoherenceAnalysis:
    """Analysis of coherence trends and patterns"""
    current_coherence: CoherenceVector
    trend_1h: float  # Coherence change over last hour
    trend_24h: float  # Coherence change over last 24 hours
    volatility: float  # Standard deviation of recent coherence
    stability_score: float  # Measure of coherence stability
    anomaly_score: float  # Anomaly detection score
    recommendations: List[str] = field(default_factory=list)


@dataclass
class CoherenceConfig:
    """Configuration for coherence computation"""
    history_retention_hours: int = 168  # 1 week
    snapshot_interval_minutes: int = 5
    trend_analysis_window_hours: int = 24
    anomaly_detection_threshold: float = 2.0  # Standard deviations
    min_coherence_threshold: float = 0.6
    coherence_weights: Tuple[float, float, float] = (0.4, 0.3, 0.3)  # PXL, IEL, Runtime
    enable_adaptive_weights: bool = True


class CoherenceMetrics:
    """
    LOGOS Coherence Metrics Computer
    
    Computes and tracks Trinity-Coherence metrics across PXL, IEL, and Runtime
    dimensions with trend analysis and anomaly detection.
    """
    
    def __init__(self, config: Optional[CoherenceConfig] = None):
        self.config = config or CoherenceConfig()
        self.logger = self._setup_logging()
        self.unified_formalisms = UnifiedFormalisms()
        
        # Coherence history and tracking
        self._coherence_history: deque = deque(maxlen=self._get_max_history_size())
        self._last_snapshot_time: Optional[datetime] = None
        
        # Component analyzers
        self._pxl_analyzer = PXLCoherenceAnalyzer()
        self._iel_analyzer = IELCoherenceAnalyzer()
        self._runtime_analyzer = RuntimeCoherenceAnalyzer()
        
        # Anomaly detection state
        self._baseline_coherence: Optional[float] = None
        self._coherence_statistics = {"mean": 0.0, "std": 0.0, "count": 0}
        
    def _setup_logging(self) -> logging.Logger:
        """Configure coherence metrics logging"""
        logger = logging.getLogger("logos.coherence_metrics")
        if not logger.handlers:
            handler = logging.StreamHandler()
            formatter = logging.Formatter(
                '%(asctime)s - %(name)s - %(levelname)s - %(message)s'
            )
            handler.setFormatter(formatter)
            logger.addHandler(handler)
            logger.setLevel(logging.INFO)
        return logger
        
    def compute_current_coherence(self) -> CoherenceVector:
        """
        Compute current system coherence across all dimensions
        
        Returns:
            CoherenceVector: Current coherence measurements
        """
        try:
            # Compute PXL coherence
            pxl_coherence = self._pxl_analyzer.compute_pxl_coherence()
            
            # Compute IEL coherence
            iel_coherence = self._iel_analyzer.compute_iel_coherence()
            
            # Compute Runtime coherence
            runtime_coherence = self._runtime_analyzer.compute_runtime_coherence()
            
            # Create coherence vector
            coherence_vector = CoherenceVector(
                pxl_coherence=pxl_coherence,
                iel_coherence=iel_coherence,
                runtime_coherence=runtime_coherence
            )
            
            self.logger.debug(f"Computed coherence: PXL={pxl_coherence:.3f}, IEL={iel_coherence:.3f}, Runtime={runtime_coherence:.3f}")
            
            return coherence_vector
            
        except Exception as e:
            self.logger.error(f"Coherence computation failed: {e}")
            # Return safe default values
            return CoherenceVector(pxl_coherence=0.5, iel_coherence=0.5, runtime_coherence=0.5)
            
    def take_coherence_snapshot(self) -> CoherenceSnapshot:
        """
        Take a coherence snapshot and add to history
        
        Returns:
            CoherenceSnapshot: Current coherence snapshot
        """
        try:
            now = datetime.now()
            coherence_vector = self.compute_current_coherence()
            
            # Compute Trinity-Coherence
            if self.config.enable_adaptive_weights:
                weights = self._compute_adaptive_weights(coherence_vector)
            else:
                weights = self.config.coherence_weights
                
            trinity_coherence = coherence_vector.weighted_trinity_coherence(weights)
            
            # Create snapshot
            snapshot = CoherenceSnapshot(
                timestamp=now,
                coherence_vector=coherence_vector,
                trinity_coherence=trinity_coherence,
                metadata={
                    "weights": weights,
                    "adaptive_weights_enabled": self.config.enable_adaptive_weights
                }
            )
            
            # Add to history
            self._coherence_history.append(snapshot)
            self._last_snapshot_time = now
            
            # Update statistics
            self._update_coherence_statistics(trinity_coherence)
            
            return snapshot
            
        except Exception as e:
            self.logger.error(f"Failed to take coherence snapshot: {e}")
            # Return safe default snapshot
            return CoherenceSnapshot(
                timestamp=datetime.now(),
                coherence_vector=CoherenceVector(0.5, 0.5, 0.5),
                trinity_coherence=0.5
            )
            
    def analyze_coherence_trends(self) -> CoherenceAnalysis:
        """
        Analyze coherence trends and patterns
        
        Returns:
            CoherenceAnalysis: Comprehensive coherence analysis
        """
        try:
            current_coherence = self.compute_current_coherence()
            
            # Compute trends
            trend_1h = self._compute_coherence_trend(hours=1)
            trend_24h = self._compute_coherence_trend(hours=24)
            
            # Compute volatility
            volatility = self._compute_coherence_volatility(hours=24)
            
            # Compute stability score
            stability_score = self._compute_stability_score()
            
            # Detect anomalies
            anomaly_score = self._detect_coherence_anomalies()
            
            # Generate recommendations
            recommendations = self._generate_coherence_recommendations(
                current_coherence, trend_1h, trend_24h, volatility, anomaly_score
            )
            
            return CoherenceAnalysis(
                current_coherence=current_coherence,
                trend_1h=trend_1h,
                trend_24h=trend_24h,
                volatility=volatility,
                stability_score=stability_score,
                anomaly_score=anomaly_score,
                recommendations=recommendations
            )
            
        except Exception as e:
            self.logger.error(f"Coherence trend analysis failed: {e}")
            return CoherenceAnalysis(
                current_coherence=CoherenceVector(0.5, 0.5, 0.5),
                trend_1h=0.0,
                trend_24h=0.0,
                volatility=0.0,
                stability_score=0.5,
                anomaly_score=0.0
            )
            
    def get_coherence_history(self, hours: int = 24) -> List[CoherenceSnapshot]:
        """
        Get coherence history for specified time window
        
        Args:
            hours: Number of hours to look back
            
        Returns:
            List[CoherenceSnapshot]: Historical coherence snapshots
        """
        cutoff_time = datetime.now() - timedelta(hours=hours)
        return [snapshot for snapshot in self._coherence_history if snapshot.timestamp >= cutoff_time]
        
    def is_coherence_degraded(self) -> bool:
        """Check if coherence has degraded below threshold"""
        if not self._coherence_history:
            return False
            
        latest_snapshot = self._coherence_history[-1]
        return latest_snapshot.trinity_coherence < self.config.min_coherence_threshold
        
    def get_coherence_statistics(self) -> Dict[str, float]:
        """Get coherence statistics"""
        return self._coherence_statistics.copy()
        
    def _get_max_history_size(self) -> int:
        """Calculate maximum history size based on retention and interval"""
        return int((self.config.history_retention_hours * 60) / self.config.snapshot_interval_minutes)
        
    def _compute_adaptive_weights(self, coherence_vector: CoherenceVector) -> Tuple[float, float, float]:
        """Compute adaptive weights based on current coherence state"""
        # Start with base weights
        α, β, γ = self.config.coherence_weights
        
        # Adjust weights based on relative coherence levels
        # Give more weight to dimensions that are performing well
        total_coherence = sum(coherence_vector)
        if total_coherence > 0:
            α_adj = α * (coherence_vector.pxl_coherence / total_coherence) * 3
            β_adj = β * (coherence_vector.iel_coherence / total_coherence) * 3
            γ_adj = γ * (coherence_vector.runtime_coherence / total_coherence) * 3
            
            # Normalize to sum to 1
            total_weight = α_adj + β_adj + γ_adj
            if total_weight > 0:
                return (α_adj / total_weight, β_adj / total_weight, γ_adj / total_weight)
                
        return self.config.coherence_weights
        
    def _compute_coherence_trend(self, hours: int) -> float:
        """Compute coherence trend over specified time window"""
        recent_snapshots = self.get_coherence_history(hours)
        
        if len(recent_snapshots) < 2:
            return 0.0
            
        # Simple linear trend calculation
        first_coherence = recent_snapshots[0].trinity_coherence
        last_coherence = recent_snapshots[-1].trinity_coherence
        
        return last_coherence - first_coherence
        
    def _compute_coherence_volatility(self, hours: int) -> float:
        """Compute coherence volatility over specified time window"""
        recent_snapshots = self.get_coherence_history(hours)
        
        if len(recent_snapshots) < 2:
            return 0.0
            
        coherence_values = [s.trinity_coherence for s in recent_snapshots]
        return statistics.stdev(coherence_values) if len(coherence_values) > 1 else 0.0
        
    def _compute_stability_score(self) -> float:
        """Compute coherence stability score"""
        recent_snapshots = self.get_coherence_history(24)  # Last 24 hours
        
        if len(recent_snapshots) < 10:
            return 0.5  # Insufficient data
            
        # Stability is inverse of volatility with bounds
        volatility = self._compute_coherence_volatility(24)
        stability = max(0.0, min(1.0, 1.0 - volatility))
        
        return stability
        
    def _detect_coherence_anomalies(self) -> float:
        """Detect anomalies in coherence using statistical methods"""
        if self._coherence_statistics["count"] < 10:
            return 0.0  # Insufficient data for anomaly detection
            
        if not self._coherence_history:
            return 0.0
            
        current_coherence = self._coherence_history[-1].trinity_coherence
        mean = self._coherence_statistics["mean"]
        std = self._coherence_statistics["std"]
        
        if std == 0:
            return 0.0
            
        # Z-score based anomaly detection
        z_score = abs(current_coherence - mean) / std
        
        # Convert to anomaly score (0-1 range)
        anomaly_score = min(1.0, z_score / self.config.anomaly_detection_threshold)
        
        return anomaly_score
        
    def _generate_coherence_recommendations(self, current_coherence: CoherenceVector,
                                          trend_1h: float, trend_24h: float,
                                          volatility: float, anomaly_score: float) -> List[str]:
        """Generate recommendations based on coherence analysis"""
        recommendations = []
        
        # Check individual dimension coherence
        if current_coherence.pxl_coherence < 0.7:
            recommendations.append("PXL coherence below threshold - review formal verification coverage")
            
        if current_coherence.iel_coherence < 0.7:
            recommendations.append("IEL coherence below threshold - validate inference rule consistency")
            
        if current_coherence.runtime_coherence < 0.7:
            recommendations.append("Runtime coherence below threshold - check operational alignment")
            
        # Check trends
        if trend_24h < -0.1:
            recommendations.append("Coherence declining over 24h - investigate system changes")
            
        if trend_1h < -0.05:
            recommendations.append("Rapid coherence decline detected - immediate attention required")
            
        # Check volatility
        if volatility > 0.2:
            recommendations.append("High coherence volatility - system may be unstable")
            
        # Check anomalies
        if anomaly_score > 0.5:
            recommendations.append("Coherence anomaly detected - unusual system behavior")
            
        # Overall recommendations
        trinity_coherence = current_coherence.trinity_coherence
        if trinity_coherence < self.config.min_coherence_threshold:
            recommendations.append("Trinity-Coherence below minimum threshold - emergency review required")
            
        if not recommendations:
            recommendations.append("Coherence metrics within normal ranges")
            
        return recommendations
        
    def _update_coherence_statistics(self, new_coherence: float) -> None:
        """Update running statistics for coherence"""
        count = self._coherence_statistics["count"]
        mean = self._coherence_statistics["mean"]
        
        # Update count and mean
        count += 1
        new_mean = mean + (new_coherence - mean) / count
        
        # Update variance (using Welford's algorithm)
        if count == 1:
            variance = 0.0
        else:
            old_variance = self._coherence_statistics["std"] ** 2
            variance = ((count - 2) * old_variance + (new_coherence - mean) * (new_coherence - new_mean)) / (count - 1)
            
        self._coherence_statistics = {
            "count": count,
            "mean": new_mean,
            "std": math.sqrt(max(0.0, variance))
        }


class PXLCoherenceAnalyzer:
    """Analyzer for PXL layer coherence"""
    
    def compute_pxl_coherence(self) -> float:
        """Compute PXL coherence based on formal verification completeness"""
        try:
            # Placeholder: implement actual PXL coherence analysis
            # This would analyze:
            # - Proof coverage completeness
            # - Logical consistency verification
            # - Axiom soundness validation
            # - Verification chain integrity
            
            base_coherence = 0.85  # Base PXL coherence
            
            # Add some variance based on system state
            import time
            variance = 0.1 * math.sin(time.time() / 100)  # Simulate temporal variance
            
            return max(0.0, min(1.0, base_coherence + variance))
            
        except Exception:
            return 0.5  # Safe default
            
            
class IELCoherenceAnalyzer:
    """Analyzer for IEL layer coherence"""
    
    def compute_iel_coherence(self) -> float:
        """Compute IEL coherence based on inference rule consistency"""
        try:
            # Placeholder: implement actual IEL coherence analysis
            # This would analyze:
            # - Inference rule completeness
            # - Cross-domain consistency
            # - Rule application coverage
            # - Logical soundness of IEL chains
            
            base_coherence = 0.80  # Base IEL coherence
            
            # Add some variance
            import time
            variance = 0.05 * math.cos(time.time() / 80)
            
            return max(0.0, min(1.0, base_coherence + variance))
            
        except Exception:
            return 0.5
            
            
class RuntimeCoherenceAnalyzer:
    """Analyzer for Runtime layer coherence"""
    
    def compute_runtime_coherence(self) -> float:
        """Compute Runtime coherence based on operational behavior alignment"""
        try:
            # Placeholder: implement actual Runtime coherence analysis
            # This would analyze:
            # - Operational behavior vs formal specification alignment
            # - Performance consistency
            # - Error rates and exception handling
            # - Resource utilization patterns
            
            base_coherence = 0.75  # Base Runtime coherence
            
            # Add some variance
            import time
            variance = 0.08 * math.sin(time.time() / 120)
            
            return max(0.0, min(1.0, base_coherence + variance))
            
        except Exception:
            return 0.5


class TrinityCoherence:
    """High-level Trinity-Coherence interface"""
    
    def __init__(self, config: Optional[CoherenceConfig] = None):
        self.coherence_metrics = CoherenceMetrics(config)
        
    def get_current_trinity_coherence(self) -> float:
        """Get current Trinity-Coherence value"""
        snapshot = self.coherence_metrics.take_coherence_snapshot()
        return snapshot.trinity_coherence
        
    def is_system_coherent(self, threshold: Optional[float] = None) -> bool:
        """Check if system is coherent above threshold"""
        current_coherence = self.get_current_trinity_coherence()
        threshold = threshold or self.coherence_metrics.config.min_coherence_threshold
        return current_coherence >= threshold
        
    def get_coherence_report(self) -> Dict[str, Any]:
        """Get comprehensive coherence report"""
        snapshot = self.coherence_metrics.take_coherence_snapshot()
        analysis = self.coherence_metrics.analyze_coherence_trends()
        
        return {
            "current_snapshot": snapshot.to_dict(),
            "trend_analysis": {
                "trend_1h": analysis.trend_1h,
                "trend_24h": analysis.trend_24h,
                "volatility": analysis.volatility,
                "stability_score": analysis.stability_score,
                "anomaly_score": analysis.anomaly_score
            },
            "recommendations": analysis.recommendations,
            "is_degraded": self.coherence_metrics.is_coherence_degraded(),
            "statistics": self.coherence_metrics.get_coherence_statistics()
        }