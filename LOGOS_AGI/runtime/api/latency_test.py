#!/usr/bin/env python3
"""
Latency + Throughput: Measure token issuance time P50/P95 on 1k requests.
Cache stable obligations. Alert on cache miss.
"""

import time
import statistics
import hashlib

# Simulate obligation cache
cache = {}

def issue_token(obligation):
    # Simulate token issuance
    key = hashlib.sha256(obligation.encode()).hexdigest()
    if key in cache:
        print(f"Cache hit for {obligation}")
        return cache[key]
    else:
        print(f"Cache miss for {obligation} - ALERT")
        # Simulate issuance time
        time.sleep(0.001)  # 1ms
        token = f"token_{key}"
        cache[key] = token
        return token

def main():
    obligations = [f"obligation_{i}" for i in range(100)] * 10  # 1k requests, some repeats
    times = []
    for obl in obligations:
        start = time.time()
        token = issue_token(obl)
        end = time.time()
        times.append(end - start)
    
    p50 = statistics.median(times)
    p95 = statistics.quantiles(times, n=20)[18]  # 95th percentile
    print(f"P50: {p50*1000:.2f}ms, P95: {p95*1000:.2f}ms")

if __name__ == "__main__":
    main()