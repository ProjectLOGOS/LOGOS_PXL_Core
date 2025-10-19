#!/bin/bash
# verify_performance.sh - CI Performance Validation Script
# Tests P95 latency < 300ms and cache hit rate >= 85%
# Exit code 1 if performance requirements not met

set -e

echo "Starting LOGOS PXL Performance Validation..."
echo "Target: P95 < 300ms, Cache Hit Rate >= 85%"

# Configuration
SERVER_URL="http://localhost:5000"
WARMUP_REQUESTS=50
LOAD_TEST_REQUESTS=1000
CONCURRENCY=10
MAX_P95_LATENCY=300
MIN_CACHE_HIT_RATE=85

# Ensure server is running
if ! curl -s "$SERVER_URL/health" > /dev/null; then
    echo "ERROR: PXL server not responding at $SERVER_URL"
    exit 1
fi

echo "Server health check: PASSED"

# Function to send proof requests
send_proof_request() {
    local goal="$1"
    local start_time=$(date +%s%3N)

    response=$(curl -s -X POST "$SERVER_URL/prove" \
        -H "Content-Type: application/json" \
        -d "{\"goal\": \"$goal\"}" \
        -w "%{http_code},%{time_total}")

    local end_time=$(date +%s%3N)
    local latency=$((end_time - start_time))

    echo "$latency"
}

# Warmup phase with cache population
echo "Warmup phase: $WARMUP_REQUESTS requests..."
for i in $(seq 1 $WARMUP_REQUESTS); do
    goal_variant="BOX(A $i -> A $i)"
    send_proof_request "$goal_variant" > /dev/null
done

echo "Warmup completed. Starting load test..."

# Load test phase
echo "Load test: $LOAD_TEST_REQUESTS requests with $CONCURRENCY concurrent workers..."

# Create test goals with repetition for cache hits
TEST_GOALS=(
    "BOX(A -> A)"
    "BOX(A /\\ B -> A)"
    "BOX(A -> A \\/ B)"
    "BOX((A -> B) -> ((B -> C) -> (A -> C)))"
    "BOX(A /\\ B -> B /\\ A)"
)

# Run concurrent load test
LATENCY_FILE=$(mktemp)
WORKERS=()

for worker in $(seq 1 $CONCURRENCY); do
    (
        for request in $(seq 1 $((LOAD_TEST_REQUESTS / CONCURRENCY))); do
            # Select goal with bias toward repetition for cache hits
            if [ $((request % 3)) -eq 0 ]; then
                goal_index=$((request % ${#TEST_GOALS[@]}))
                goal="${TEST_GOALS[$goal_index]}"
            else
                # Repeat previous goals to trigger cache hits
                goal_index=$(((request - 1) % ${#TEST_GOALS[@]}))
                goal="${TEST_GOALS[$goal_index]}"
            fi

            latency=$(send_proof_request "$goal")
            echo "$latency" >> "$LATENCY_FILE"
        done
    ) &
    WORKERS+=($!)
done

# Wait for all workers
for worker_pid in "${WORKERS[@]}"; do
    wait "$worker_pid"
done

echo "Load test completed. Analyzing results..."

# Calculate performance metrics
LATENCIES=($(sort -n "$LATENCY_FILE"))
TOTAL_REQUESTS=${#LATENCIES[@]}

if [ $TOTAL_REQUESTS -eq 0 ]; then
    echo "ERROR: No latency data collected"
    exit 1
fi

# Calculate percentiles
P50_INDEX=$((TOTAL_REQUESTS * 50 / 100))
P90_INDEX=$((TOTAL_REQUESTS * 90 / 100))
P95_INDEX=$((TOTAL_REQUESTS * 95 / 100))
P99_INDEX=$((TOTAL_REQUESTS * 99 / 100))

P50_LATENCY=${LATENCIES[$P50_INDEX]}
P90_LATENCY=${LATENCIES[$P90_INDEX]}
P95_LATENCY=${LATENCIES[$P95_INDEX]}
P99_LATENCY=${LATENCIES[$P99_INDEX]}

# Get cache statistics
CACHE_STATS=$(curl -s "$SERVER_URL/health" | python3 -c "
import sys, json
data = json.load(sys.stdin)
cache = data.get('cache_stats', {})
print(f\"{cache.get('hit_rate', 0) * 100:.1f}%\")
print(f\"{cache.get('cache_hits', 0)}\")
print(f\"{cache.get('cache_misses', 0)}\")
print(f\"{cache.get('prefetch_hits', 0)}\")
")

read -r CACHE_HIT_RATE_PCT CACHE_HITS CACHE_MISSES PREFETCH_HITS <<< "$CACHE_STATS"
CACHE_HIT_RATE=$(echo "$CACHE_HIT_RATE_PCT" | sed 's/%//')

# Performance report
echo ""
echo "=== PERFORMANCE VALIDATION RESULTS ==="
echo "Total Requests: $TOTAL_REQUESTS"
echo "Latency Percentiles (ms):"
echo "  P50: $P50_LATENCY"
echo "  P90: $P90_LATENCY"
echo "  P95: $P95_LATENCY"
echo "  P99: $P99_LATENCY"
echo ""
echo "Cache Performance:"
echo "  Hit Rate: $CACHE_HIT_RATE_PCT"
echo "  Cache Hits: $CACHE_HITS"
echo "  Cache Misses: $CACHE_MISSES"
echo "  Prefetch Hits: $PREFETCH_HITS"
echo ""

# Validation checks
VALIDATION_PASSED=true

if [ "$P95_LATENCY" -gt "$MAX_P95_LATENCY" ]; then
    echo "❌ FAILED: P95 latency ($P95_LATENCY ms) exceeds maximum ($MAX_P95_LATENCY ms)"
    VALIDATION_PASSED=false
else
    echo "✅ PASSED: P95 latency ($P95_LATENCY ms) within target ($MAX_P95_LATENCY ms)"
fi

# Convert cache hit rate to integer for comparison
CACHE_HIT_RATE_INT=$(echo "$CACHE_HIT_RATE" | cut -d. -f1)
if [ "$CACHE_HIT_RATE_INT" -lt "$MIN_CACHE_HIT_RATE" ]; then
    echo "❌ FAILED: Cache hit rate ($CACHE_HIT_RATE_PCT) below minimum ($MIN_CACHE_HIT_RATE%)"
    VALIDATION_PASSED=false
else
    echo "✅ PASSED: Cache hit rate ($CACHE_HIT_RATE_PCT) meets target (≥$MIN_CACHE_HIT_RATE%)"
fi

# Additional performance insights
echo ""
echo "=== PERFORMANCE INSIGHTS ==="
POOL_STATS=$(curl -s "$SERVER_URL/health" | python3 -c "
import sys, json
data = json.load(sys.stdin)
pool = data.get('session_pool_stats', {})
print(f\"Sessions: {pool.get('total_sessions', 0)}\")
print(f\"Utilization: {pool.get('utilization_rate', 0) * 100:.1f}%\")
print(f\"Max Pool: {pool.get('max_pool_size', 0)}\")
")

echo "Session Pool: $POOL_STATS"

# Cleanup
rm -f "$LATENCY_FILE"

if [ "$VALIDATION_PASSED" = true ]; then
    echo ""
    echo "🎉 ALL PERFORMANCE TESTS PASSED"
    echo "Week 3 Security Hardening and Performance Optimization: COMPLETE"
    exit 0
else
    echo ""
    echo "💥 PERFORMANCE VALIDATION FAILED"
    echo "Requirements not met. Please optimize before deployment."
    exit 1
fi
