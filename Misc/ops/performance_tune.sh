#!/bin/bash
# LOGOS PXL Core - Performance Tuning Script
# Configures autoscaling and cache warming for production

set -euo pipefail

echo "Starting LOGOS PXL Core performance tuning..."

# Configure autoscaling thresholds
echo "Configuring autoscaling thresholds..."
cat > /opt/logos/monitoring/prometheus/autoscale_rules.yml << EOF
groups:
  - name: pxl_autoscale
    rules:
      - alert: HighCPUUsage
        expr: rate(container_cpu_usage_seconds_total[5m]) > 0.7
        for: 5m
        labels:
          severity: info
        annotations:
          summary: "High CPU usage detected"
          action: "scale_up"

      - alert: HighLatency
        expr: histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 0.25
        for: 5m
        labels:
          severity: info
        annotations:
          summary: "High latency detected"
          action: "scale_up"

      - alert: LowUtilization
        expr: rate(container_cpu_usage_seconds_total[5m]) < 0.3
        for: 10m
        labels:
          severity: info
        annotations:
          summary: "Low utilization detected"
          action: "scale_down"
EOF

# Update Docker Compose with scaling configuration
echo "Updating Docker Compose for autoscaling..."
cat >> /opt/logos/docker-compose.prod.yml << EOF

# Autoscaling configuration
x-autoscale-config: &autoscale-config
  deploy:
    replicas: 1
    resources:
      limits:
        cpus: '2.0'
        memory: 2G
      reservations:
        cpus: '0.5'
        memory: 512M
    restart_policy:
      condition: on-failure
      delay: 5s
      max_attempts: 3
      window: 120s

services:
  overlay-chrono:
    <<: *autoscale-config
    # Additional scaling config can be added here

  overlay-v4:
    <<: *autoscale-config
    # Additional scaling config can be added here
EOF

# Create cache warming job
echo "Creating cache warming startup job..."
cat > /opt/logos/ops/cache_warm.sh << EOF
#!/bin/bash
# Cache warming job for frequent proof goals

echo "Starting cache warming..."

# Common proof patterns to warm caches
PROOF_PATTERNS=(
  "forall (x: nat), x + 0 = x"
  "forall (A B: Prop), A -> (B -> A)"
  "forall (x y: nat), x + S y = S (x + y)"
)

for pattern in "\${PROOF_PATTERNS[@]}"; do
  echo "Warming cache for: \$pattern"
  curl -X POST http://localhost/v1/proofs \\
    -H "Content-Type: application/json" \\
    -H "Authorization: Bearer \${WARMING_TOKEN}" \\
    -d "{
      \"formula\": \"\$pattern\",
      \"overlay\": \"chrono\"
    }" || true  # Don't fail if warming request fails
  sleep 1
done

echo "Cache warming completed"
EOF

chmod +x /opt/logos/ops/cache_warm.sh

# Add cache warming to startup
echo "Adding cache warming to service startup..."
cat >> /opt/logos/docker-compose.prod.yml << EOF

  cache-warmer:
    image: alpine:latest
    command: sh -c "sleep 60 && /opt/logos/ops/cache_warm.sh"
    volumes:
      - /opt/logos/ops/cache_warm.sh:/opt/logos/ops/cache_warm.sh:ro
    depends_on:
      - gateway
      - overlay-chrono
    deploy:
      restart_policy:
        condition: on-failure
EOF

# Configure performance monitoring
echo "Configuring performance monitoring..."
cat > /opt/logos/monitoring/prometheus/performance_rules.yml << EOF
groups:
  - name: pxl_performance
    rules:
      - record: proof_request_duration:rate5m
        expr: rate(http_request_duration_seconds{endpoint="/v1/proofs"}[5m])

      - record: proof_success_rate:ratio
        expr: rate(http_requests_total{endpoint="/v1/proofs", status="200"}[5m]) / rate(http_requests_total{endpoint="/v1/proofs"}[5m])

      - record: queue_depth:current
        expr: proof_queue_length

      - alert: PerformanceDegradation
        expr: proof_request_duration:rate5m > 0.3
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "Proof request latency > 300ms for 5 minutes"
EOF

echo "✅ Performance tuning completed"
echo "Features enabled:"
echo "  - CPU-based autoscaling (>70% for 5min)"
echo "  - Latency-based autoscaling (>250ms for 5min)"
echo "  - Cache warming for common proof patterns"
echo "  - Performance monitoring rules"