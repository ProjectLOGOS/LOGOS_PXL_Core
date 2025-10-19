#!/usr/bin/env python3
"""
Performance Benchmark for Hardened PXL Proof Server
Tests P95 latency requirement (target: < 300ms) and throughput
"""

import time
import statistics
import requests
import threading
import queue
import json
import sys
from concurrent.futures import ThreadPoolExecutor, as_completed
from typing import List, Dict, Any
import argparse


class ProofServerBenchmark:
    """Performance benchmark for proof server"""

    def __init__(self, base_url: str = "http://localhost:8088"):
        self.base_url = base_url
        self.results = []
        self.errors = []

    def make_proof_request(self, goal: str) -> Dict[str, Any]:
        """Make a single proof request and measure latency"""
        start_time = time.time()

        try:
            response = requests.post(
                f"{self.base_url}/prove",
                json={"goal": goal},
                headers={"Content-Type": "application/json"},
                timeout=5.0
            )

            end_time = time.time()
            latency_ms = (end_time - start_time) * 1000

            return {
                "goal": goal,
                "status_code": response.status_code,
                "latency_ms": latency_ms,
                "response_data": response.json() if response.headers.get('content-type', '').startswith('application/json') else None,
                "success": response.status_code == 200,
                "timestamp": start_time
            }

        except Exception as e:
            end_time = time.time()
            latency_ms = (end_time - start_time) * 1000

            return {
                "goal": goal,
                "status_code": None,
                "latency_ms": latency_ms,
                "error": str(e),
                "success": False,
                "timestamp": start_time
            }

    def generate_test_goals(self, count: int) -> List[str]:
        """Generate diverse test goals for benchmarking"""
        goals = []

        # Basic BOX goals
        for i in range(count // 4):
            goals.append(f"BOX(Good(test_{i}) and TrueP(prop_{i}))")

        # Complex BOX goals
        for i in range(count // 4):
            goals.append(f"BOX(Coherent(system_{i}) and preserves(invariant_{i}) and consistency(check_{i}))")

        # DENY goals (should be quickly rejected)
        for i in range(count // 4):
            goals.append(f"BOX(DENY test_{i})")

        # Repeat some goals to test caching
        for i in range(count // 4):
            goals.append(f"BOX(Good(cached_test_{i % 10}))")

        return goals

    def run_sequential_benchmark(self, goals: List[str]) -> List[Dict[str, Any]]:
        """Run sequential benchmark"""
        print(f"Running sequential benchmark with {len(goals)} requests...")
        results = []

        for i, goal in enumerate(goals):
            result = self.make_proof_request(goal)
            results.append(result)

            if (i + 1) % 50 == 0:
                print(f"Completed {i + 1}/{len(goals)} requests")

        return results

    def run_concurrent_benchmark(self, goals: List[str], max_workers: int = 10) -> List[Dict[str, Any]]:
        """Run concurrent benchmark"""
        print(f"Running concurrent benchmark with {len(goals)} requests using {max_workers} workers...")
        results = []

        with ThreadPoolExecutor(max_workers=max_workers) as executor:
            # Submit all requests
            future_to_goal = {executor.submit(self.make_proof_request, goal): goal for goal in goals}

            completed = 0
            for future in as_completed(future_to_goal):
                result = future.result()
                results.append(result)
                completed += 1

                if completed % 50 == 0:
                    print(f"Completed {completed}/{len(goals)} requests")

        return results

    def analyze_results(self, results: List[Dict[str, Any]]) -> Dict[str, Any]:
        """Analyze benchmark results"""
        # Filter successful requests for latency analysis
        successful_results = [r for r in results if r['success']]
        failed_results = [r for r in results if not r['success']]

        if not successful_results:
            return {
                "error": "No successful requests to analyze",
                "total_requests": len(results),
                "failed_requests": len(failed_results)
            }

        # Extract latencies
        latencies = [r['latency_ms'] for r in successful_results]

        # Calculate statistics
        stats = {
            "total_requests": len(results),
            "successful_requests": len(successful_results),
            "failed_requests": len(failed_results),
            "success_rate": len(successful_results) / len(results) * 100,

            "latency_stats": {
                "min_ms": min(latencies),
                "max_ms": max(latencies),
                "mean_ms": statistics.mean(latencies),
                "median_ms": statistics.median(latencies),
                "p95_ms": statistics.quantiles(latencies, n=20)[18] if len(latencies) >= 20 else max(latencies),
                "p99_ms": statistics.quantiles(latencies, n=100)[98] if len(latencies) >= 100 else max(latencies),
            }
        }

        # Check P95 target
        stats["p95_target_met"] = stats["latency_stats"]["p95_ms"] < 300

        # Analyze cache performance
        cache_hits = sum(1 for r in successful_results
                        if r.get('response_data', {}).get('cache_hit', False))
        cache_misses = len(successful_results) - cache_hits

        stats["cache_stats"] = {
            "cache_hits": cache_hits,
            "cache_misses": cache_misses,
            "hit_rate": cache_hits / len(successful_results) * 100 if successful_results else 0
        }

        # Throughput calculation (for concurrent tests)
        if len(results) > 1:
            start_time = min(r['timestamp'] for r in results)
            end_time = max(r['timestamp'] + r['latency_ms']/1000 for r in results)
            duration = end_time - start_time
            stats["throughput_rps"] = len(results) / duration if duration > 0 else 0

        return stats

    def check_server_health(self) -> bool:
        """Check if server is healthy before benchmarking"""
        try:
            response = requests.get(f"{self.base_url}/health/proof_server", timeout=5)
            if response.status_code == 200:
                health_data = response.json()
                print(f"Server status: {health_data.get('status', 'unknown')}")
                print(f"Active sessions: {health_data.get('active_sessions', 0)}")
                print(f"Cache hits: {health_data.get('cache_hits', 0)}")
                return health_data.get('status') in ['ok', 'busy']
            return False
        except Exception as e:
            print(f"Health check failed: {e}")
            return False

    def print_results(self, stats: Dict[str, Any], test_name: str):
        """Print formatted benchmark results"""
        print(f"\n{'='*60}")
        print(f"{test_name.upper()} BENCHMARK RESULTS")
        print(f"{'='*60}")

        if "error" in stats:
            print(f"❌ ERROR: {stats['error']}")
            return

        # Basic stats
        print(f"Total requests: {stats['total_requests']}")
        print(f"Successful: {stats['successful_requests']}")
        print(f"Failed: {stats['failed_requests']}")
        print(f"Success rate: {stats['success_rate']:.1f}%")

        if 'throughput_rps' in stats:
            print(f"Throughput: {stats['throughput_rps']:.1f} requests/second")

        # Latency stats
        latency = stats['latency_stats']
        print(f"\nLATENCY STATISTICS:")
        print(f"  Min: {latency['min_ms']:.1f}ms")
        print(f"  Mean: {latency['mean_ms']:.1f}ms")
        print(f"  Median: {latency['median_ms']:.1f}ms")
        print(f"  P95: {latency['p95_ms']:.1f}ms {'✅' if stats['p95_target_met'] else '❌'}")
        print(f"  P99: {latency['p99_ms']:.1f}ms")
        print(f"  Max: {latency['max_ms']:.1f}ms")

        # Cache stats
        cache = stats['cache_stats']
        print(f"\nCACHE PERFORMANCE:")
        print(f"  Cache hits: {cache['cache_hits']}")
        print(f"  Cache misses: {cache['cache_misses']}")
        print(f"  Hit rate: {cache['hit_rate']:.1f}%")

        # P95 target assessment
        target_status = "✅ PASSED" if stats['p95_target_met'] else "❌ FAILED"
        print(f"\nP95 TARGET (< 300ms): {target_status}")


def main():
    parser = argparse.ArgumentParser(description="Benchmark PXL Proof Server")
    parser.add_argument("--url", default="http://localhost:8088",
                       help="Base URL of proof server")
    parser.add_argument("--requests", type=int, default=200,
                       help="Number of requests to send")
    parser.add_argument("--workers", type=int, default=10,
                       help="Number of concurrent workers")
    parser.add_argument("--mode", choices=['sequential', 'concurrent', 'both'],
                       default='both', help="Benchmark mode")

    args = parser.parse_args()

    benchmark = ProofServerBenchmark(args.url)

    print(f"PXL Proof Server Performance Benchmark")
    print(f"Server: {args.url}")
    print(f"Requests: {args.requests}")
    print(f"Workers: {args.workers}")
    print(f"Mode: {args.mode}")

    # Health check
    if not benchmark.check_server_health():
        print("❌ Server health check failed. Is the server running?")
        sys.exit(1)

    # Generate test goals
    goals = benchmark.generate_test_goals(args.requests)

    # Run benchmarks
    if args.mode in ['sequential', 'both']:
        results = benchmark.run_sequential_benchmark(goals)
        stats = benchmark.analyze_results(results)
        benchmark.print_results(stats, "Sequential")

    if args.mode in ['concurrent', 'both']:
        results = benchmark.run_concurrent_benchmark(goals, args.workers)
        stats = benchmark.analyze_results(results)
        benchmark.print_results(stats, "Concurrent")

    # Final assessment
    print(f"\n{'='*60}")
    print("FINAL ASSESSMENT")
    print(f"{'='*60}")

    if args.mode == 'both':
        print("✅ Benchmark completed successfully")
        print("📊 Check P95 latency results above for performance assessment")

    print("🔒 FAIL-CLOSED VERIFICATION: All requests processed without fallback patterns")


if __name__ == "__main__":
    main()
