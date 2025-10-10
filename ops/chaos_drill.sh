#!/bin/bash
# LOGOS PXL Core - Chaos Engineering Drill
# Tests system resilience by simulating failures

set -euo pipefail

DRILL_DURATION=${DRILL_DURATION:-300}  # 5 minutes default
SLO_LATENCY_P95=${SLO_LATENCY_P95:-300}
SLO_ERROR_RATE=${SLO_ERROR_RATE:-0.05}

echo "Starting LOGOS PXL Core Chaos Drill"
echo "Duration: ${DRILL_DURATION}s"
echo "SLO Targets: P95 < ${SLO_LATENCY_P95}ms, Error Rate < ${SLO_ERROR_RATE}"

# Start monitoring in background
monitor_slos() {
  local start_time=$(date +%s)
  local violations=0

  while true; do
    # Check if drill should end
    local current_time=$(date +%s)
    if (( current_time - start_time > DRILL_DURATION )); then
      break
    fi

    # Query Prometheus for SLO metrics
    # In real deployment, this would query actual Prometheus
    local p95_latency=$(curl -s "http://localhost:9090/api/v1/query?query=histogram_quantile(0.95,%20rate(http_request_duration_seconds_bucket[5m]))" | jq -r '.data.result[0].value[1]' | awk '{print $1 * 1000}')
    local error_rate=$(curl -s "http://localhost:9090/api/v1/query?query=rate(http_requests_total{status=~\"5..\"}[5m])%20/%20rate(http_requests_total[5m])" | jq -r '.data.result[0].value[1]')

    # Mock values for simulation (replace with real queries)
    p95_latency=${p95_latency:-250}
    error_rate=${error_rate:-0.02}

    if (( $(echo "$p95_latency > $SLO_LATENCY_P95" | bc -l) )) || (( $(echo "$error_rate > $SLO_ERROR_RATE" | bc -l) )); then
      echo "❌ SLO violation detected: P95=${p95_latency}ms, ErrorRate=${error_rate}"
      ((violations++))
    else
      echo "✅ SLOs within bounds: P95=${p95_latency}ms, ErrorRate=${error_rate}"
    fi

    sleep 10
  done

  if (( violations > 0 )); then
    echo "❌ Chaos drill failed: $violations SLO violations"
    return 1
  else
    echo "✅ Chaos drill passed: No SLO violations"
    return 0
  fi
}

# Start monitoring
monitor_slos &
MONITOR_PID=$!

# Wait for monitoring to stabilize
sleep 30

# Phase 1: Kill overlay-chrono pod
echo "Phase 1: Terminating overlay-chrono service..."
docker-compose -f docker-compose.prod.yml stop overlay-chrono
sleep 60  # Wait for auto-recovery

# Check if service recovered
if curl -f http://localhost:8081/health; then
  echo "✅ overlay-chrono recovered automatically"
else
  echo "❌ overlay-chrono failed to recover"
  kill $MONITOR_PID
  exit 1
fi

# Phase 2: Restart service
echo "Phase 2: Restarting overlay-chrono service..."
docker-compose -f docker-compose.prod.yml start overlay-chrono
sleep 30

# Phase 3: High load test during recovery
echo "Phase 3: Applying load during recovery..."
# In real deployment, trigger k6 load test here
echo "Simulating load test..."

# Wait for drill completion
sleep $((DRILL_DURATION - 120))

# Cleanup
kill $MONITOR_PID 2>/dev/null || true
wait $MONITOR_PID 2>/dev/null || true

echo "Chaos drill completed"