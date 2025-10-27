#!/usr/bin/env python3
"""
Performance Profiling Module
Timing decorators and metrics collection for LOGOS PXL Core
Week 3: Performance Optimization Implementation
"""

import time
import json
import statistics
import threading
import functools
from typing import Dict, List, Any, Callable, Optional
from dataclasses import dataclass, asdict
from collections import defaultdict, OrderedDict
import os
import logging

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)


@dataclass
class PerformanceMetric:
    """Single performance measurement"""

    function_name: str
    duration_ms: float
    timestamp: float
    thread_id: int
    args_hash: Optional[str] = None


@dataclass
class PerformanceStats:
    """Aggregated performance statistics"""

    function_name: str
    call_count: int
    total_duration_ms: float
    mean_duration_ms: float
    median_duration_ms: float
    p90_duration_ms: float
    p95_duration_ms: float
    p99_duration_ms: float
    min_duration_ms: float
    max_duration_ms: float
    last_updated: float


class PerformanceMonitor:
    """Thread-safe performance monitoring and metrics collection"""

    def __init__(self, log_file: str = "logs/performance.json"):
        self.log_file = log_file
        self.metrics: Dict[str, List[PerformanceMetric]] = defaultdict(list)
        self.lock = threading.Lock()
        self.max_metrics_per_function = 10000  # Prevent memory overflow

        # Ensure logs directory exists
        os.makedirs(os.path.dirname(log_file), exist_ok=True)

        logger.info(f"Performance monitor initialized, logging to {log_file}")

    def record_metric(self, metric: PerformanceMetric):
        """Record a performance metric"""
        with self.lock:
            function_metrics = self.metrics[metric.function_name]
            function_metrics.append(metric)

            # Maintain size limit (keep recent metrics)
            if len(function_metrics) > self.max_metrics_per_function:
                function_metrics[:] = function_metrics[-self.max_metrics_per_function // 2 :]

    def get_stats(self, function_name: str) -> Optional[PerformanceStats]:
        """Get performance statistics for a specific function"""
        with self.lock:
            if function_name not in self.metrics:
                return None

            durations = [m.duration_ms for m in self.metrics[function_name]]

            if not durations:
                return None

            # Calculate percentiles
            sorted_durations = sorted(durations)
            n = len(sorted_durations)

            def percentile(p: float) -> float:
                k = (n - 1) * p / 100
                f = int(k)
                c = k - f
                if f + 1 < n:
                    return sorted_durations[f] * (1 - c) + sorted_durations[f + 1] * c
                else:
                    return sorted_durations[f]

            return PerformanceStats(
                function_name=function_name,
                call_count=len(durations),
                total_duration_ms=sum(durations),
                mean_duration_ms=statistics.mean(durations),
                median_duration_ms=statistics.median(durations),
                p90_duration_ms=percentile(90),
                p95_duration_ms=percentile(95),
                p99_duration_ms=percentile(99),
                min_duration_ms=min(durations),
                max_duration_ms=max(durations),
                last_updated=time.time(),
            )

    def get_all_stats(self) -> Dict[str, PerformanceStats]:
        """Get performance statistics for all monitored functions"""
        stats = {}
        for function_name in list(self.metrics.keys()):
            function_stats = self.get_stats(function_name)
            if function_stats:
                stats[function_name] = function_stats
        return stats

    def log_metrics_to_file(self):
        """Write current metrics to JSON log file"""
        stats = self.get_all_stats()

        if not stats:
            return

        log_entry = {
            "timestamp": time.time(),
            "metrics": {name: asdict(stat) for name, stat in stats.items()},
        }

        try:
            # Append to log file
            with open(self.log_file, "a") as f:
                f.write(json.dumps(log_entry) + "\n")

            logger.info(f"Performance metrics logged to {self.log_file}")

        except Exception as e:
            logger.error(f"Failed to write performance log: {e}")

    def clear_metrics(self, function_name: Optional[str] = None):
        """Clear metrics for a specific function or all functions"""
        with self.lock:
            if function_name:
                if function_name in self.metrics:
                    del self.metrics[function_name]
            else:
                self.metrics.clear()

    def get_summary_report(self) -> Dict[str, Any]:
        """Generate a comprehensive performance summary report"""
        stats = self.get_all_stats()

        if not stats:
            return {"error": "No performance data available"}

        # Overall system performance
        all_p95s = [stat.p95_duration_ms for stat in stats.values()]
        all_means = [stat.mean_duration_ms for stat in stats.values()]

        # Critical endpoints analysis
        critical_functions = ["prove", "validate_proof_with_serapi", "countermodel"]
        critical_stats = {name: stats.get(name) for name in critical_functions if name in stats}

        # Performance targets assessment
        p95_target_300ms = all([stat.p95_duration_ms < 300 for stat in stats.values()])

        return {
            "summary": {
                "total_functions_monitored": len(stats),
                "overall_max_p95_ms": max(all_p95s) if all_p95s else 0,
                "overall_mean_p95_ms": statistics.mean(all_p95s) if all_p95s else 0,
                "overall_mean_duration_ms": statistics.mean(all_means) if all_means else 0,
                "p95_target_300ms_met": p95_target_300ms,
            },
            "critical_endpoints": critical_stats,
            "all_functions": {name: asdict(stat) for name, stat in stats.items()},
            "generated_at": time.time(),
        }


# Global performance monitor instance
performance_monitor = PerformanceMonitor()


def performance_timer(include_args: bool = False):
    """
    Decorator to measure function execution time

    Args:
        include_args: Whether to include a hash of arguments in metrics
    """

    def decorator(func: Callable) -> Callable:
        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            start_time = time.time()

            try:
                result = func(*args, **kwargs)
                success = True
            except Exception as e:
                success = False
                raise
            finally:
                end_time = time.time()
                duration_ms = (end_time - start_time) * 1000

                # Create args hash if requested
                args_hash = None
                if include_args:
                    args_str = str(args) + str(sorted(kwargs.items()))
                    args_hash = str(hash(args_str))

                # Record metric
                metric = PerformanceMetric(
                    function_name=func.__name__,
                    duration_ms=duration_ms,
                    timestamp=start_time,
                    thread_id=threading.get_ident(),
                    args_hash=args_hash,
                )

                performance_monitor.record_metric(metric)

                # Log slow operations
                if duration_ms > 1000:  # Log operations > 1 second
                    logger.warning(f"Slow operation: {func.__name__} took {duration_ms:.2f}ms")

            return result

        return wrapper

    return decorator


def concurrent_load_test(
    target_function: Callable, args_list: List[tuple], num_threads: int = 10
) -> Dict[str, Any]:
    """
    Execute concurrent load test on a target function

    Args:
        target_function: Function to test
        args_list: List of argument tuples for function calls
        num_threads: Number of concurrent threads

    Returns:
        Load test results with timing statistics
    """
    import concurrent.futures

    start_time = time.time()
    results = []
    errors = []

    def execute_call(args):
        try:
            call_start = time.time()
            result = target_function(*args)
            call_end = time.time()
            return {
                "success": True,
                "duration_ms": (call_end - call_start) * 1000,
                "result": result,
            }
        except Exception as e:
            call_end = time.time()
            return {
                "success": False,
                "duration_ms": (call_end - call_start) * 1000,
                "error": str(e),
            }

    # Execute concurrent load test
    with concurrent.futures.ThreadPoolExecutor(max_workers=num_threads) as executor:
        futures = [executor.submit(execute_call, args) for args in args_list]

        for future in concurrent.futures.as_completed(futures):
            result = future.result()
            if result["success"]:
                results.append(result)
            else:
                errors.append(result)

    end_time = time.time()

    # Calculate statistics
    if results:
        durations = [r["duration_ms"] for r in results]
        sorted_durations = sorted(durations)
        n = len(sorted_durations)

        def percentile(p: float) -> float:
            k = (n - 1) * p / 100
            f = int(k)
            c = k - f
            if f + 1 < n:
                return sorted_durations[f] * (1 - c) + sorted_durations[f + 1] * c
            else:
                return sorted_durations[f]

        return {
            "total_calls": len(args_list),
            "successful_calls": len(results),
            "failed_calls": len(errors),
            "success_rate": len(results) / len(args_list) * 100,
            "total_duration_s": end_time - start_time,
            "throughput_rps": len(args_list) / (end_time - start_time),
            "latency_stats": {
                "min_ms": min(durations),
                "max_ms": max(durations),
                "mean_ms": statistics.mean(durations),
                "median_ms": statistics.median(durations),
                "p90_ms": percentile(90),
                "p95_ms": percentile(95),
                "p99_ms": percentile(99),
            },
            "errors": errors[:10],  # First 10 errors
        }
    else:
        return {
            "total_calls": len(args_list),
            "successful_calls": 0,
            "failed_calls": len(errors),
            "success_rate": 0,
            "error": "All calls failed",
            "errors": errors,
        }


# Background thread for periodic metric logging
def start_performance_logging_thread(interval_seconds: int = 60):
    """Start background thread for periodic performance logging"""

    def logging_worker():
        while True:
            time.sleep(interval_seconds)
            performance_monitor.log_metrics_to_file()

    thread = threading.Thread(target=logging_worker, daemon=True)
    thread.start()
    logger.info(f"Performance logging thread started with {interval_seconds}s interval")


if __name__ == "__main__":
    # Example usage and testing

    @performance_timer(include_args=True)
    def example_function(delay: float, data: str):
        time.sleep(delay)
        return f"processed: {data}"

    # Test the performance monitoring
    print("Testing performance monitoring...")

    for i in range(100):
        example_function(0.001 * (i % 10), f"data_{i}")

    # Get statistics
    stats = performance_monitor.get_stats("example_function")
    if stats:
        print(f"\nFunction: {stats.function_name}")
        print(f"Calls: {stats.call_count}")
        print(f"Mean: {stats.mean_duration_ms:.2f}ms")
        print(f"P95: {stats.p95_duration_ms:.2f}ms")
        print(f"P99: {stats.p99_duration_ms:.2f}ms")

    # Generate report
    report = performance_monitor.get_summary_report()
    print(f"\nSummary Report:")
    print(json.dumps(report["summary"], indent=2))
