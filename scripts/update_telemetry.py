#!/usr/bin/env python3
"""
Telemetry Update Script - Cycle Metrics Aggregation and Reporting

Aggregates telemetry data from multiple cycles, computes trends and insights,
and generates comprehensive reports for the autonomous IEL evaluation and
refinement system.

Features:
- Aggregate metrics from multiple JSONL telemetry files
- Calculate performance trends and improvement metrics
- Generate cycle-over-cycle comparison reports
- Detect anomalies and performance degradations
- Export aggregated data for dashboard visualization

Part of the LOGOS AGI v1.0 autonomous reasoning framework.
"""

import argparse
import json
import logging
import statistics
import sys
from datetime import datetime, timedelta
from pathlib import Path
from typing import Dict, List, Any, Optional, Tuple
from collections import defaultdict
from dataclasses import dataclass
import glob


@dataclass
class CycleMetrics:
    """Metrics for a single evaluation cycle"""
    timestamp: datetime
    cycle_id: str
    gaps_detected: int
    iels_evaluated: int
    high_quality_iels: int
    mean_quality_score: float
    refinement_generated: int
    pruned_count: int
    memory_usage_mb: float
    cpu_usage_percent: float
    cycle_duration_sec: float
    errors_count: int


@dataclass
class AggregatedMetrics:
    """Aggregated metrics across multiple cycles"""
    total_cycles: int
    date_range: Tuple[datetime, datetime]

    # Performance metrics
    avg_gaps_per_cycle: float
    avg_iels_per_cycle: float
    avg_quality_score: float
    quality_trend: str  # "improving", "stable", "declining"

    # Resource usage
    avg_memory_usage: float
    max_memory_usage: float
    avg_cpu_usage: float
    max_cpu_usage: float

    # System health
    total_errors: int
    error_rate: float
    uptime_percentage: float

    # Efficiency metrics
    avg_cycle_duration: float
    throughput_iels_per_hour: float
    refinement_success_rate: float


class TelemetryAggregator:
    """Main telemetry aggregation and reporting system"""

    def __init__(self):
        self.logger = logging.getLogger(__name__)
        self.cycles: List[CycleMetrics] = []

    def load_telemetry_files(self, pattern: str) -> None:
        """Load telemetry data from multiple JSONL files"""
        files = glob.glob(pattern)
        self.logger.info(f"Loading telemetry from {len(files)} files...")

        for file_path in files:
            try:
                self._load_single_file(file_path)
            except Exception as e:
                self.logger.error(f"Failed to load {file_path}: {e}")

        self.logger.info(f"Loaded {len(self.cycles)} cycles from telemetry data")

    def _load_single_file(self, file_path: str) -> None:
        """Load telemetry data from a single JSONL file"""
        with open(file_path, 'r', encoding='utf-8') as f:
            for line_num, line in enumerate(f, 1):
                try:
                    record = json.loads(line.strip())
                    cycle_metrics = self._parse_telemetry_record(record)
                    if cycle_metrics:
                        self.cycles.append(cycle_metrics)
                except json.JSONDecodeError as e:
                    self.logger.warning(f"Invalid JSON at {file_path}:{line_num}: {e}")
                except Exception as e:
                    self.logger.error(f"Error parsing {file_path}:{line_num}: {e}")

    def _parse_telemetry_record(self, record: Dict[str, Any]) -> Optional[CycleMetrics]:
        """Parse a single telemetry record into CycleMetrics"""
        try:
            timestamp_str = record.get('timestamp', '')
            if not timestamp_str:
                return None

            timestamp = datetime.fromisoformat(timestamp_str.replace('Z', '+00:00'))

            # Handle different record types
            event_type = record.get('event_type', '')
            data = record.get('data', {})

            if event_type == 'iel_evaluation_cycle':
                return CycleMetrics(
                    timestamp=timestamp,
                    cycle_id=record.get('cycle_id', f"cycle_{int(timestamp.timestamp())}"),
                    gaps_detected=0,  # Will be aggregated from other records
                    iels_evaluated=data.get('total_iels_evaluated', 0),
                    high_quality_iels=data.get('high_quality_iels', 0),
                    mean_quality_score=data.get('evaluation_summary', {}).get('mean_score', 0.0),
                    refinement_generated=0,  # Will be updated
                    pruned_count=0,  # Will be updated
                    memory_usage_mb=data.get('memory_usage_mb', 0.0),
                    cpu_usage_percent=data.get('cpu_usage_percent', 0.0),
                    cycle_duration_sec=data.get('cycle_duration_sec', 0.0),
                    errors_count=1 if data.get('error') else 0
                )

            elif event_type == 'gaps_detected':
                return CycleMetrics(
                    timestamp=timestamp,
                    cycle_id=f"gap_cycle_{int(timestamp.timestamp())}",
                    gaps_detected=data.get('count', 0),
                    iels_evaluated=0,
                    high_quality_iels=0,
                    mean_quality_score=0.0,
                    refinement_generated=0,
                    pruned_count=0,
                    memory_usage_mb=0.0,
                    cpu_usage_percent=0.0,
                    cycle_duration_sec=0.0,
                    errors_count=0
                )

            return None

        except Exception as e:
            self.logger.error(f"Failed to parse record: {e}")
            return None

    def aggregate_metrics(self) -> AggregatedMetrics:
        """Aggregate metrics across all loaded cycles"""
        if not self.cycles:
            raise ValueError("No cycles loaded for aggregation")

        # Sort cycles by timestamp
        self.cycles.sort(key=lambda c: c.timestamp)

        # Calculate basic aggregations
        total_cycles = len(self.cycles)
        date_range = (self.cycles[0].timestamp, self.cycles[-1].timestamp)

        # Performance aggregations
        gaps_per_cycle = [c.gaps_detected for c in self.cycles if c.gaps_detected > 0]
        iels_per_cycle = [c.iels_evaluated for c in self.cycles if c.iels_evaluated > 0]
        quality_scores = [c.mean_quality_score for c in self.cycles if c.mean_quality_score > 0]

        avg_gaps_per_cycle = statistics.mean(gaps_per_cycle) if gaps_per_cycle else 0.0
        avg_iels_per_cycle = statistics.mean(iels_per_cycle) if iels_per_cycle else 0.0
        avg_quality_score = statistics.mean(quality_scores) if quality_scores else 0.0

        # Calculate quality trend
        quality_trend = self._calculate_trend(quality_scores)

        # Resource usage
        memory_values = [c.memory_usage_mb for c in self.cycles if c.memory_usage_mb > 0]
        cpu_values = [c.cpu_usage_percent for c in self.cycles if c.cpu_usage_percent > 0]

        avg_memory_usage = statistics.mean(memory_values) if memory_values else 0.0
        max_memory_usage = max(memory_values) if memory_values else 0.0
        avg_cpu_usage = statistics.mean(cpu_values) if cpu_values else 0.0
        max_cpu_usage = max(cpu_values) if cpu_values else 0.0

        # System health
        total_errors = sum(c.errors_count for c in self.cycles)
        error_rate = total_errors / total_cycles if total_cycles > 0 else 0.0
        uptime_percentage = (1.0 - error_rate) * 100.0

        # Efficiency metrics
        durations = [c.cycle_duration_sec for c in self.cycles if c.cycle_duration_sec > 0]
        avg_cycle_duration = statistics.mean(durations) if durations else 0.0

        # Calculate throughput
        total_iels = sum(c.iels_evaluated for c in self.cycles)
        total_time_hours = (date_range[1] - date_range[0]).total_seconds() / 3600
        throughput_iels_per_hour = total_iels / total_time_hours if total_time_hours > 0 else 0.0

        # Refinement success rate (mock calculation)
        total_refined = sum(c.refinement_generated for c in self.cycles)
        total_pruned = sum(c.pruned_count for c in self.cycles)
        refinement_success_rate = total_refined / (total_pruned + 1) if total_pruned > 0 else 1.0

        return AggregatedMetrics(
            total_cycles=total_cycles,
            date_range=date_range,
            avg_gaps_per_cycle=avg_gaps_per_cycle,
            avg_iels_per_cycle=avg_iels_per_cycle,
            avg_quality_score=avg_quality_score,
            quality_trend=quality_trend,
            avg_memory_usage=avg_memory_usage,
            max_memory_usage=max_memory_usage,
            avg_cpu_usage=avg_cpu_usage,
            max_cpu_usage=max_cpu_usage,
            total_errors=total_errors,
            error_rate=error_rate,
            uptime_percentage=uptime_percentage,
            avg_cycle_duration=avg_cycle_duration,
            throughput_iels_per_hour=throughput_iels_per_hour,
            refinement_success_rate=refinement_success_rate
        )

    def _calculate_trend(self, values: List[float]) -> str:
        """Calculate trend direction from time series data"""
        if len(values) < 3:
            return "stable"

        # Simple linear trend calculation
        n = len(values)
        x_values = list(range(n))

        # Calculate slope
        x_mean = statistics.mean(x_values)
        y_mean = statistics.mean(values)

        numerator = sum((x_values[i] - x_mean) * (values[i] - y_mean) for i in range(n))
        denominator = sum((x_values[i] - x_mean) ** 2 for i in range(n))

        if denominator == 0:
            return "stable"

        slope = numerator / denominator

        if slope > 0.01:
            return "improving"
        elif slope < -0.01:
            return "declining"
        else:
            return "stable"

    def generate_report(self, aggregated: AggregatedMetrics, output_path: str) -> None:
        """Generate comprehensive telemetry report"""
        report = {
            "report_metadata": {
                "generated_at": datetime.now().isoformat(),
                "report_type": "autonomous_iel_telemetry_aggregate",
                "version": "1.0"
            },
            "summary": {
                "total_cycles": aggregated.total_cycles,
                "date_range": {
                    "start": aggregated.date_range[0].isoformat(),
                    "end": aggregated.date_range[1].isoformat(),
                    "duration_days": (aggregated.date_range[1] - aggregated.date_range[0]).days
                },
                "system_health": {
                    "uptime_percentage": round(aggregated.uptime_percentage, 2),
                    "error_rate": round(aggregated.error_rate, 4),
                    "total_errors": aggregated.total_errors
                }
            },
            "performance_metrics": {
                "iel_evaluation": {
                    "avg_gaps_per_cycle": round(aggregated.avg_gaps_per_cycle, 2),
                    "avg_iels_per_cycle": round(aggregated.avg_iels_per_cycle, 2),
                    "avg_quality_score": round(aggregated.avg_quality_score, 3),
                    "quality_trend": aggregated.quality_trend,
                    "throughput_iels_per_hour": round(aggregated.throughput_iels_per_hour, 2)
                },
                "resource_usage": {
                    "avg_memory_usage_mb": round(aggregated.avg_memory_usage, 2),
                    "max_memory_usage_mb": round(aggregated.max_memory_usage, 2),
                    "avg_cpu_usage_percent": round(aggregated.avg_cpu_usage, 2),
                    "max_cpu_usage_percent": round(aggregated.max_cpu_usage, 2)
                },
                "efficiency": {
                    "avg_cycle_duration_sec": round(aggregated.avg_cycle_duration, 2),
                    "refinement_success_rate": round(aggregated.refinement_success_rate, 3)
                }
            },
            "detailed_cycles": [
                {
                    "cycle_id": cycle.cycle_id,
                    "timestamp": cycle.timestamp.isoformat(),
                    "gaps_detected": cycle.gaps_detected,
                    "iels_evaluated": cycle.iels_evaluated,
                    "high_quality_iels": cycle.high_quality_iels,
                    "quality_score": round(cycle.mean_quality_score, 3),
                    "duration_sec": round(cycle.cycle_duration_sec, 2),
                    "errors": cycle.errors_count
                }
                for cycle in self.cycles
            ],
            "recommendations": self._generate_recommendations(aggregated)
        }

        # Write report
        Path(output_path).parent.mkdir(parents=True, exist_ok=True)
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(report, f, indent=2, ensure_ascii=False)

        self.logger.info(f"Telemetry report generated: {output_path}")

    def _generate_recommendations(self, aggregated: AggregatedMetrics) -> List[str]:
        """Generate actionable recommendations based on metrics"""
        recommendations = []

        if aggregated.error_rate > 0.05:
            recommendations.append("High error rate detected. Review system logs and consider stability improvements.")

        if aggregated.quality_trend == "declining":
            recommendations.append("Quality trend is declining. Investigate IEL generation and refinement processes.")

        if aggregated.avg_cpu_usage > 80.0:
            recommendations.append("High CPU usage detected. Consider optimization or resource scaling.")

        if aggregated.max_memory_usage > 1024:  # 1GB
            recommendations.append("High memory usage detected. Review memory management and potential leaks.")

        if aggregated.throughput_iels_per_hour < 1.0:
            recommendations.append("Low throughput detected. Optimize evaluation pipeline for better performance.")

        if aggregated.refinement_success_rate < 0.5:
            recommendations.append("Low refinement success rate. Review refinement algorithms and thresholds.")

        if not recommendations:
            recommendations.append("System operating within normal parameters. Continue monitoring.")

        return recommendations


def main():
    """Main entry point for telemetry update script"""
    parser = argparse.ArgumentParser(description="LOGOS AGI Telemetry Aggregator")
    parser.add_argument('--input', default='metrics/*.jsonl',
                       help='Input telemetry files pattern (default: metrics/*.jsonl)')
    parser.add_argument('--output', default='reports/telemetry_report.json',
                       help='Output report file (default: reports/telemetry_report.json)')
    parser.add_argument('--verbose', '-v', action='store_true',
                       help='Enable verbose logging')

    args = parser.parse_args()

    # Setup logging
    logging.basicConfig(
        level=logging.INFO if args.verbose else logging.WARNING,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s'
    )

    try:
        aggregator = TelemetryAggregator()

        # Load telemetry data
        print(f"Loading telemetry data from: {args.input}")
        aggregator.load_telemetry_files(args.input)

        if not aggregator.cycles:
            print("No telemetry data found. Check input pattern.")
            return 1

        # Aggregate metrics
        print("Aggregating metrics...")
        aggregated_metrics = aggregator.aggregate_metrics()

        # Generate report
        print(f"Generating report: {args.output}")
        aggregator.generate_report(aggregated_metrics, args.output)

        # Print summary
        print(f"\nTelemetry Update Complete:")
        print(f"  Cycles processed: {aggregated_metrics.total_cycles}")
        print(f"  Quality trend: {aggregated_metrics.quality_trend}")
        print(f"  Average quality: {aggregated_metrics.avg_quality_score:.3f}")
        print(f"  System uptime: {aggregated_metrics.uptime_percentage:.1f}%")
        print(f"  Report saved: {args.output}")

        return 0

    except Exception as e:
        logging.error(f"Telemetry update failed: {e}")
        return 1


if __name__ == '__main__':
    sys.exit(main())
