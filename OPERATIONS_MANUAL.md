# LOGOS_PXL_Core v0.5 - Operations Manual

**Version**: v0.5-rc1  
**Last Updated**: October 19, 2025  
**Scope**: Production Operations, Maintenance, and Emergency Procedures

---

## 🎯 **Operations Overview**

This manual provides comprehensive operational procedures for maintaining LOGOS_PXL_Core v0.5 in production environments. It covers routine maintenance, performance optimization, security monitoring, incident response, and disaster recovery procedures.

---

## 📊 **System Health Monitoring**

### **Key Performance Indicators (KPIs)**

| Metric | Target | Critical Threshold | Monitoring Frequency |
|--------|--------|-------------------|---------------------|
| Verification Ratio | ≥94% | <90% | Real-time |
| P95 Latency | <300ms | >500ms | Every 30s |
| Cache Hit Rate | ≥85% | <70% | Every 60s |
| System Uptime | ≥99.9% | <99% | Continuous |
| Session Pool Utilization | <80% | >90% | Every 15s |
| Memory Usage | <80% | >95% | Every 30s |

### **Monitoring Commands**

#### **Real-Time Health Check**
```bash
# Quick system status
curl -s http://localhost:8088/health | jq '{status: .status, sessions: .session_pool.total_sessions, ready: .ready}'

# Comprehensive metrics
curl -s http://localhost:8088/metrics | jq '{
  verification_ratio: .logos_pxl_verification_ratio_percent,
  p95_latency: .logos_pxl_p95_latency_ms,
  cache_hit_rate: .logos_pxl_cache_hit_rate_percent,
  uptime: .logos_pxl_uptime_seconds
}'
```

#### **Continuous Monitoring Script**
```bash
#!/bin/bash
# monitor_pxl.sh - Continuous health monitoring

while true; do
  TIMESTAMP=$(date '+%Y-%m-%d %H:%M:%S')
  HEALTH=$(curl -s http://localhost:8088/metrics)
  
  VERIFICATION_RATIO=$(echo $HEALTH | jq -r '.logos_pxl_verification_ratio_percent // "N/A"')
  P95_LATENCY=$(echo $HEALTH | jq -r '.logos_pxl_p95_latency_ms // "N/A"')
  CACHE_HIT_RATE=$(echo $HEALTH | jq -r '.logos_pxl_cache_hit_rate_percent // "N/A"')
  
  echo "$TIMESTAMP | Verification: $VERIFICATION_RATIO% | P95: ${P95_LATENCY}ms | Cache: $CACHE_HIT_RATE%"
  
  # Alert conditions
  if [ "$(echo "$VERIFICATION_RATIO < 90" | bc -l)" = "1" ]; then
    echo "ALERT: Verification ratio below 90%: $VERIFICATION_RATIO%"
  fi
  
  if [ "$(echo "$P95_LATENCY > 300" | bc -l)" = "1" ]; then
    echo "ALERT: P95 latency exceeds 300ms: ${P95_LATENCY}ms"
  fi
  
  sleep 30
done
```

### **Prometheus Queries**

#### **SLA Monitoring**
```promql
# Verification ratio over time
logos_pxl_verification_ratio_percent

# P95 latency trend
rate(logos_pxl_p95_latency_ms[5m])

# Cache performance
logos_pxl_cache_hit_rate_percent

# Session pool saturation
logos_pxl_session_pool_busy / logos_pxl_session_pool_total
```

#### **Alert Conditions**
```yaml
# prometheus-alerts.yml
groups:
- name: logos-pxl-production
  rules:
  - alert: VerificationRatioLow
    expr: logos_pxl_verification_ratio_percent < 90
    for: 1m
    labels:
      severity: critical
    annotations:
      summary: "Verification ratio below 90%"
      description: "Current ratio: {{ $value }}%"
      runbook: "Check proof server health and SerAPI connections"

  - alert: HighLatencyP95
    expr: logos_pxl_p95_latency_ms > 300
    for: 2m
    labels:
      severity: warning
    annotations:
      summary: "P95 latency exceeds 300ms"
      description: "Current P95: {{ $value }}ms"
      runbook: "Check cache performance and session pool utilization"

  - alert: SessionPoolSaturated
    expr: (logos_pxl_session_pool_busy / logos_pxl_session_pool_total) > 0.9
    for: 30s
    labels:
      severity: warning
    annotations:
      summary: "Session pool >90% utilized"
      description: "Utilization: {{ $value | humanizePercentage }}"
      runbook: "Scale session pool or add instances"
```

---

## ⚙️ **Routine Maintenance**

### **Daily Operations**

#### **Morning Health Check** (09:00 UTC)
```bash
#!/bin/bash
# daily_health_check.sh

echo "=== LOGOS PXL Core Daily Health Check ==="
echo "Date: $(date)"

# 1. System Status
echo "1. System Status:"
curl -s http://localhost:8088/health | jq '{status: .status, ready: .ready, timestamp: .timestamp}'

# 2. Performance Metrics
echo "2. Performance Metrics:"
METRICS=$(curl -s http://localhost:8088/metrics)
echo "   Verification Ratio: $(echo $METRICS | jq -r '.logos_pxl_verification_ratio_percent')%"
echo "   P95 Latency: $(echo $METRICS | jq -r '.logos_pxl_p95_latency_ms')ms"
echo "   Cache Hit Rate: $(echo $METRICS | jq -r '.logos_pxl_cache_hit_rate_percent')%"
echo "   Uptime: $(echo $METRICS | jq -r '.logos_pxl_uptime_seconds')s"

# 3. Resource Usage
echo "3. Resource Usage:"
echo "   Session Pool: $(echo $METRICS | jq -r '.logos_pxl_session_pool_busy')/$(echo $METRICS | jq -r '.logos_pxl_session_pool_total') busy"
echo "   Cache Size: $(echo $METRICS | jq -r '.logos_pxl_cache_size') entries"

# 4. Error Check
echo "4. Recent Errors:"
tail -n 50 logs/pxl-server.log | grep -i error | tail -5

# 5. Performance Test
echo "5. Performance Test:"
START_TIME=$(date +%s%3N)
RESPONSE=$(curl -s -X POST http://localhost:8088/prove \
  -H "Content-Type: application/json" \
  -d '{"goal": "BOX(A -> A)"}')
END_TIME=$(date +%s%3N)
LATENCY=$((END_TIME - START_TIME))

echo "   Test Latency: ${LATENCY}ms"
echo "   Test Result: $(echo $RESPONSE | jq -r '.ok')"

echo "=== Health Check Complete ==="
```

#### **Log Rotation** (02:00 UTC)
```bash
#!/bin/bash
# rotate_logs.sh

LOG_DIR="/app/logs"
ARCHIVE_DIR="/app/logs/archive"
DATE=$(date +%Y%m%d)

# Create archive directory
mkdir -p $ARCHIVE_DIR

# Rotate performance logs
if [ -f "$LOG_DIR/performance.json" ]; then
  cp "$LOG_DIR/performance.json" "$ARCHIVE_DIR/performance_$DATE.json"
  echo '{}' > "$LOG_DIR/performance.json"
fi

# Rotate server logs  
if [ -f "$LOG_DIR/pxl-server.log" ]; then
  gzip -c "$LOG_DIR/pxl-server.log" > "$ARCHIVE_DIR/pxl-server_$DATE.log.gz"
  > "$LOG_DIR/pxl-server.log"  # Clear current log
fi

# Clean old archives (keep 30 days)
find $ARCHIVE_DIR -name "*.gz" -mtime +30 -delete
find $ARCHIVE_DIR -name "*.json" -mtime +30 -delete

echo "Log rotation completed: $(date)"
```

### **Weekly Operations**

#### **Performance Review** (Sundays 12:00 UTC)
```bash
#!/bin/bash
# weekly_performance_review.sh

WEEK_START=$(date -d '7 days ago' '+%Y-%m-%d')
TODAY=$(date '+%Y-%m-%d')

echo "=== Weekly Performance Review: $WEEK_START to $TODAY ==="

# 1. Aggregate Performance Data
echo "1. Performance Summary:"
find logs/archive -name "performance_*.json" -newer $(date -d "$WEEK_START" '+%Y%m%d') | while read file; do
  echo "Processing: $file"
  # Extract key metrics from daily performance logs
  jq -r '.endpoints[] | select(.name | contains("prove")) | "P95: \(.p95_duration_ms)ms, Calls: \(.call_count)"' "$file" 2>/dev/null || echo "No data"
done

# 2. Error Analysis
echo "2. Error Analysis:"
ERROR_COUNT=$(find logs/archive -name "pxl-server_*.log.gz" -newer $(date -d "$WEEK_START" '+%Y%m%d') -exec zcat {} \; | grep -c "ERROR" || echo "0")
echo "   Total Errors This Week: $ERROR_COUNT"

# 3. Capacity Planning
echo "3. Capacity Planning:"
CURRENT_METRICS=$(curl -s http://localhost:8088/metrics)
CURRENT_UTILIZATION=$(echo $CURRENT_METRICS | jq -r '(.logos_pxl_session_pool_busy / .logos_pxl_session_pool_total) * 100')
echo "   Current Session Pool Utilization: $CURRENT_UTILIZATION%"

if [ "$(echo "$CURRENT_UTILIZATION > 60" | bc -l)" = "1" ]; then
  echo "   RECOMMENDATION: Consider increasing session pool size"
fi

# 4. Cache Performance
CACHE_HIT_RATE=$(echo $CURRENT_METRICS | jq -r '.logos_pxl_cache_hit_rate_percent')
echo "   Cache Hit Rate: $CACHE_HIT_RATE%"

if [ "$(echo "$CACHE_HIT_RATE < 80" | bc -l)" = "1" ]; then
  echo "   RECOMMENDATION: Review cache TTL settings or add more cache layers"
fi

echo "=== Weekly Review Complete ==="
```

#### **Security Audit** (Sundays 14:00 UTC)
```bash
#!/bin/bash
# weekly_security_audit.sh

echo "=== Weekly Security Audit: $(date) ==="

# 1. HMAC Authentication Status
echo "1. HMAC Authentication:"
AUTH_STATUS=$(env | grep ENABLE_HMAC_AUTH | cut -d'=' -f2)
if [ "$AUTH_STATUS" = "true" ]; then
  echo "   ✅ HMAC Authentication: ENABLED"
else
  echo "   ⚠️  HMAC Authentication: DISABLED"
fi

# 2. Failed Authentication Attempts
echo "2. Security Events:"
FAILED_AUTH=$(grep -c "401\|Invalid signature\|Timestamp" logs/archive/pxl-server_*.log.gz 2>/dev/null || echo "0")
echo "   Failed Auth Attempts This Week: $FAILED_AUTH"

# 3. Rate Limiting Analysis
echo "3. Rate Limiting:"
HIGH_FREQUENCY_IPS=$(zcat logs/archive/pxl-server_*.log.gz 2>/dev/null | grep -E "POST /prove" | awk '{print $1}' | sort | uniq -c | sort -nr | head -5)
echo "   Top Request Sources:"
echo "$HIGH_FREQUENCY_IPS"

# 4. SSL/TLS Status (if applicable)
echo "4. SSL/TLS Configuration:"
if command -v openssl >/dev/null; then
  SSL_CHECK=$(echo | timeout 3 openssl s_client -connect localhost:8088 2>/dev/null | grep "Verify return code")
  echo "   $SSL_CHECK"
else
  echo "   SSL check not available (plain HTTP deployment)"
fi

echo "=== Security Audit Complete ==="
```

### **Monthly Operations**

#### **Capacity Planning Review** (First Monday of Month)
```bash
#!/bin/bash
# monthly_capacity_review.sh

echo "=== Monthly Capacity Planning Review: $(date) ==="

# 1. Resource Trends Analysis
echo "1. Resource Usage Trends:"

# CPU and Memory (if monitoring available)
echo "   Analyzing 30-day performance trends..."

# Session Pool Growth
CURRENT_POOL_SIZE=$(curl -s http://localhost:8088/metrics | jq -r '.logos_pxl_session_pool_total')
echo "   Current Session Pool Size: $CURRENT_POOL_SIZE"

# Request Volume Analysis
TOTAL_REQUESTS=$(curl -s http://localhost:8088/metrics | jq -r '(.logos_pxl_cache_hits_total + .logos_pxl_cache_misses_total)')
echo "   Total Requests (cached): $TOTAL_REQUESTS"

# 2. Performance Degradation Analysis
echo "2. Performance Analysis:"
CURRENT_P95=$(curl -s http://localhost:8088/metrics | jq -r '.logos_pxl_p95_latency_ms')
echo "   Current P95 Latency: ${CURRENT_P95}ms"

if [ "$(echo "$CURRENT_P95 > 250" | bc -l)" = "1" ]; then
  echo "   📊 TREND: Latency approaching threshold (300ms)"
  echo "   💡 RECOMMENDATION: Proactive scaling recommended"
fi

# 3. Scaling Recommendations
echo "3. Scaling Recommendations:"

# Calculate growth rate (simplified)
CACHE_SIZE=$(curl -s http://localhost:8088/metrics | jq -r '.logos_pxl_cache_size')
UTILIZATION=$(curl -s http://localhost:8088/metrics | jq -r '(.logos_pxl_session_pool_busy / .logos_pxl_session_pool_total) * 100')

echo "   Cache Utilization: $CACHE_SIZE entries"
echo "   Pool Utilization: $UTILIZATION%"

if [ "$(echo "$UTILIZATION > 70" | bc -l)" = "1" ]; then
  NEW_POOL_SIZE=$((CURRENT_POOL_SIZE + 5))
  echo "   🚀 RECOMMENDATION: Increase pool size to $NEW_POOL_SIZE"
  echo "   📝 ACTION: Set PXL_POOL_SIZE=$NEW_POOL_SIZE"
fi

echo "=== Capacity Review Complete ==="
```

---

## 🚨 **Incident Response**

### **Alert Severity Levels**

| Severity | Description | Response Time | Escalation |
|----------|-------------|---------------|------------|
| **Critical** | System down, verification ratio <85% | 5 minutes | Immediate escalation |
| **High** | P95 >500ms, verification ratio <90% | 15 minutes | After 30 minutes |
| **Medium** | P95 >300ms, cache hit rate <70% | 1 hour | After 2 hours |
| **Low** | Minor performance degradation | 4 hours | After 8 hours |

### **Critical Incident Response**

#### **Scenario 1: System Completely Down**
**Symptoms**: Health endpoint unreachable, HTTP 5xx errors
**Immediate Actions** (0-5 minutes):
```bash
# 1. Verify system status
curl -f http://localhost:8088/health || echo "SYSTEM DOWN"

# 2. Check service status
docker-compose ps  # or kubectl get pods

# 3. Check logs for immediate cause
tail -50 logs/pxl-server.log | grep -E "ERROR|CRITICAL|FATAL"

# 4. Attempt service restart
docker-compose restart pxl-prover  # or kubectl rollout restart deployment/pxl-prover

# 5. Verify recovery
sleep 30
curl http://localhost:8088/health
```

**Investigation Actions** (5-15 minutes):
```bash
# 1. Resource exhaustion check
free -h
df -h
ps aux | grep python | head -10

# 2. Network connectivity
netstat -tuln | grep 8088
ss -tuln | grep 8088

# 3. SerAPI process status
pgrep -f sertop
ps aux | grep coq

# 4. Detailed log analysis
grep -A 10 -B 10 "FATAL\|CRITICAL" logs/pxl-server.log | tail -50
```

#### **Scenario 2: High Latency (P95 >500ms)**
**Symptoms**: Slow responses, timeouts, user complaints
**Immediate Actions**:
```bash
# 1. Check current performance
curl -s http://localhost:8088/metrics | jq '.logos_pxl_p95_latency_ms'

# 2. Session pool status
curl -s http://localhost:8088/health | jq '.session_pool'

# 3. Check for session pool saturation
UTILIZATION=$(curl -s http://localhost:8088/metrics | jq -r '(.logos_pxl_session_pool_busy / .logos_pxl_session_pool_total) * 100')
echo "Session pool utilization: $UTILIZATION%"

# 4. Scale session pool if saturated (>90%)
if [ "$(echo "$UTILIZATION > 90" | bc -l)" = "1" ]; then
  export PXL_POOL_SIZE=15  # Increase from default 5
  docker-compose restart pxl-prover
fi

# 5. Monitor improvement
watch -n 10 'curl -s http://localhost:8088/metrics | jq ".logos_pxl_p95_latency_ms"'
```

#### **Scenario 3: Low Verification Ratio (<90%)**
**Symptoms**: Failed proofs, incorrect results, SerAPI errors
**Immediate Actions**:
```bash
# 1. Check verification ratio
RATIO=$(curl -s http://localhost:8088/metrics | jq -r '.logos_pxl_verification_ratio_percent')
echo "Current verification ratio: $RATIO%"

# 2. Test basic proof functionality
TEST_RESULT=$(curl -s -X POST http://localhost:8088/prove \
  -H "Content-Type: application/json" \
  -d '{"goal": "BOX(A -> A)"}' | jq -r '.ok')
echo "Basic proof test result: $TEST_RESULT"

# 3. Check SerAPI connectivity
curl -s http://localhost:8088/health | jq '.session_pool.active_sessions'

# 4. Restart SerAPI sessions
docker-compose restart pxl-prover

# 5. Run verification test
python integration_test_suite.py --url http://localhost:8088
```

### **Post-Incident Procedures**

#### **Incident Documentation Template**
```markdown
# Incident Report: [INCIDENT_ID]

**Date**: [YYYY-MM-DD]
**Duration**: [START_TIME] - [END_TIME] UTC
**Severity**: [Critical/High/Medium/Low]
**Status**: [Resolved/Investigating/Mitigated]

## Summary
Brief description of the incident and impact.

## Timeline
- **[TIME]**: Initial alert
- **[TIME]**: Response team notified
- **[TIME]**: Investigation started
- **[TIME]**: Root cause identified
- **[TIME]**: Mitigation applied
- **[TIME]**: Service restored
- **[TIME]**: Monitoring confirmed

## Root Cause
Detailed analysis of what caused the incident.

## Impact
- **Users Affected**: [Number/Percentage]
- **Duration**: [Minutes/Hours]
- **SLA Impact**: [Yes/No - details]

## Resolution
Steps taken to resolve the incident.

## Prevention
Actions to prevent similar incidents:
- [ ] Monitoring improvements
- [ ] Code changes
- [ ] Infrastructure changes
- [ ] Process improvements

## Lessons Learned
Key takeaways and improvements identified.
```

---

## 🔧 **Performance Optimization**

### **Latency Optimization**

#### **Cache Optimization**
```bash
# 1. Monitor cache performance
CACHE_STATS=$(curl -s http://localhost:8088/metrics | jq '{
  hit_rate: .logos_pxl_cache_hit_rate_percent,
  cache_size: .logos_pxl_cache_size,
  hits: .logos_pxl_cache_hits_total,
  misses: .logos_pxl_cache_misses_total,
  prefetch_hits: .logos_pxl_cache_prefetch_hits_total
}')
echo "$CACHE_STATS"

# 2. Optimize cache TTL
# If hit rate < 80%: Increase TTL
export PXL_CACHE_TTL=600  # Increase from 300s to 600s
docker-compose restart pxl-prover

# 3. Monitor improvement
watch -n 30 'curl -s http://localhost:8088/metrics | jq ".logos_pxl_cache_hit_rate_percent"'
```

#### **Session Pool Tuning**
```bash
# 1. Monitor session pool efficiency
SESSION_STATS=$(curl -s http://localhost:8088/metrics | jq '{
  total: .logos_pxl_session_pool_total,
  busy: .logos_pxl_session_pool_busy,
  utilization: (.logos_pxl_session_pool_busy / .logos_pxl_session_pool_total * 100)
}')
echo "$SESSION_STATS"

# 2. Scale session pool based on utilization
UTILIZATION=$(curl -s http://localhost:8088/metrics | jq -r '(.logos_pxl_session_pool_busy / .logos_pxl_session_pool_total) * 100')

if [ "$(echo "$UTILIZATION > 80" | bc -l)" = "1" ]; then
  echo "Scaling session pool..."
  export PXL_POOL_SIZE=15  # Scale up
  docker-compose restart pxl-prover
elif [ "$(echo "$UTILIZATION < 30" | bc -l)" = "1" ]; then
  echo "Scaling down session pool..."
  export PXL_POOL_SIZE=3   # Scale down
  docker-compose restart pxl-prover
fi
```

### **Memory Optimization**

#### **Memory Usage Monitoring**
```bash
# 1. Monitor system memory
free -h

# 2. Monitor container memory (Docker)
docker stats --no-stream | grep pxl

# 3. Monitor cache memory usage
CACHE_SIZE=$(curl -s http://localhost:8088/metrics | jq -r '.logos_pxl_cache_size')
echo "Cache entries: $CACHE_SIZE (max: 1000)"

# 4. Clean up if needed (cache auto-manages, but can restart if necessary)
if [ "$CACHE_SIZE" -gt 950 ]; then
  echo "Cache nearly full, restarting for cleanup"
  docker-compose restart pxl-prover
fi
```

### **Network Optimization**

#### **Connection Pooling**
```bash
# 1. Monitor connection status
netstat -tuln | grep 8088
ss -s

# 2. Optimize Waitress server settings (in serve_pxl.py)
# threads=8          # Increase from 4
# connection_limit=200  # Increase from 100
# channel_timeout=120   # Increase from 60

# 3. Load balancer optimization (if using)
# - connection pooling
# - keep-alive settings
# - timeout configuration
```

---

## 🔒 **Security Operations**

### **HMAC Authentication Management**

#### **Key Rotation Procedure**
```bash
#!/bin/bash
# rotate_hmac_key.sh

# 1. Generate new secret key
NEW_KEY=$(openssl rand -hex 32)
echo "Generated new HMAC key: $NEW_KEY"

# 2. Update environment (use your deployment method)
echo "HMAC_SECRET_KEY=$NEW_KEY" >> .env.new

# 3. Graceful rollover (supports multiple keys temporarily)
export HMAC_SECRET_KEY_NEW="$NEW_KEY"
export HMAC_SECRET_KEY_OLD="$HMAC_SECRET_KEY"

# 4. Restart service with new key
docker-compose restart pxl-prover

# 5. Update client configurations
echo "Update client configurations with new key: $NEW_KEY"
echo "Remove old key after 24-hour grace period"

# 6. Schedule old key removal
echo "export HMAC_SECRET_KEY=$NEW_KEY && unset HMAC_SECRET_KEY_OLD" | at now + 1 day
```

#### **Security Audit Commands**
```bash
# 1. Check failed authentication attempts
grep -c "401\|Invalid signature" logs/pxl-server.log

# 2. Monitor authentication patterns
grep "X-Signature\|HMAC" logs/pxl-server.log | tail -20

# 3. Verify HMAC configuration
env | grep HMAC_SECRET_KEY | wc -l  # Should be 1
env | grep ENABLE_HMAC_AUTH          # Should show 'true'

# 4. Test authentication endpoint
curl -X POST http://localhost:8088/prove \
  -H "Content-Type: application/json" \
  -d '{"goal": "BOX(A -> A)"}' \
  -w "%{http_code}\n"
# Should return 401 if HMAC enabled and no auth headers provided
```

### **Access Control**

#### **Rate Limiting Monitoring**
```bash
# 1. Monitor request patterns
awk '{print $1}' logs/access.log | sort | uniq -c | sort -nr | head -10

# 2. Check for potential abuse
grep -c "POST /prove" logs/access.log | awk '{print "Requests per hour: " $1}'

# 3. Implement temporary rate limiting (nginx example)
# limit_req_zone $binary_remote_addr zone=pxl:10m rate=60r/m;
# limit_req zone=pxl burst=10 nodelay;
```

---

## 🔄 **Backup and Recovery**

### **Backup Procedures**

#### **Configuration Backup**
```bash
#!/bin/bash
# backup_config.sh

BACKUP_DIR="/backups/logos-pxl"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
BACKUP_FILE="logos-pxl-config_$TIMESTAMP.tar.gz"

mkdir -p $BACKUP_DIR

# 1. Create configuration backup
tar -czf "$BACKUP_DIR/$BACKUP_FILE" \
  --exclude='logs/archive' \
  --exclude='*.log' \
  docker-compose.prod.yml \
  .env \
  configs/ \
  kubernetes/ \
  monitoring/ \
  logs/performance.json

# 2. Verify backup
tar -tzf "$BACKUP_DIR/$BACKUP_FILE" | head -10

# 3. Clean old backups (keep 30 days)
find $BACKUP_DIR -name "logos-pxl-config_*.tar.gz" -mtime +30 -delete

echo "Backup completed: $BACKUP_FILE"
```

#### **State Export** (for migration)
```bash
#!/bin/bash
# export_state.sh

EXPORT_DIR="/exports/logos-pxl"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)

mkdir -p $EXPORT_DIR

# 1. Export current metrics
curl -s http://localhost:8088/metrics > "$EXPORT_DIR/metrics_$TIMESTAMP.json"

# 2. Export health status
curl -s http://localhost:8088/health > "$EXPORT_DIR/health_$TIMESTAMP.json"

# 3. Export performance data
cp logs/performance.json "$EXPORT_DIR/performance_$TIMESTAMP.json"

# 4. Export kernel hash for verification
KERNEL_HASH=$(curl -s http://localhost:8088/health | jq -r '.kernel_hash')
echo "$KERNEL_HASH" > "$EXPORT_DIR/kernel_hash_$TIMESTAMP.txt"

echo "State exported to: $EXPORT_DIR"
```

### **Recovery Procedures**

#### **Full System Recovery**
```bash
#!/bin/bash
# recover_system.sh

BACKUP_FILE="$1"
if [ -z "$BACKUP_FILE" ]; then
  echo "Usage: $0 <backup_file>"
  exit 1
fi

echo "Starting system recovery from: $BACKUP_FILE"

# 1. Stop current services
docker-compose down

# 2. Restore configuration
tar -xzf "$BACKUP_FILE" -C /

# 3. Verify configuration
ls -la docker-compose.prod.yml .env configs/

# 4. Restart services
docker-compose -f docker-compose.prod.yml up -d

# 5. Wait for startup
sleep 30

# 6. Verify recovery
curl -f http://localhost:8088/health && echo "Recovery successful" || echo "Recovery failed"

# 7. Run integration tests
python integration_test_suite.py --url http://localhost:8088
```

#### **Performance Recovery** (after degradation)
```bash
#!/bin/bash
# recover_performance.sh

echo "Starting performance recovery procedures..."

# 1. Clear cache and restart
docker-compose restart pxl-prover
sleep 30

# 2. Verify baseline performance
INITIAL_P95=$(curl -s http://localhost:8088/metrics | jq -r '.logos_pxl_p95_latency_ms')
echo "Initial P95 latency: ${INITIAL_P95}ms"

# 3. Optimize session pool
export PXL_POOL_SIZE=10
docker-compose restart pxl-prover
sleep 30

# 4. Optimize cache settings
export PXL_CACHE_TTL=600
docker-compose restart pxl-prover
sleep 30

# 5. Verify improvement
FINAL_P95=$(curl -s http://localhost:8088/metrics | jq -r '.logos_pxl_p95_latency_ms')
echo "Final P95 latency: ${FINAL_P95}ms"

IMPROVEMENT=$(echo "scale=2; $INITIAL_P95 - $FINAL_P95" | bc)
echo "Performance improvement: ${IMPROVEMENT}ms"

if [ "$(echo "$FINAL_P95 < 300" | bc -l)" = "1" ]; then
  echo "✅ Performance recovery successful"
else
  echo "⚠️  Performance still degraded, manual investigation required"
fi
```

---

## 📞 **Emergency Contacts and Escalation**

### **Escalation Matrix**

| Incident Type | Primary | Secondary | Manager |
|---------------|---------|-----------|---------|
| System Down | DevOps Lead | Senior Engineer | Engineering Manager |
| Security Breach | Security Engineer | CISO | Director of Security |
| Performance Degradation | Platform Engineer | DevOps Lead | Engineering Manager |
| Data Loss/Corruption | Senior Engineer | Architect | CTO |

### **Emergency Procedures**

#### **Security Incident Response**
1. **Immediate**: Isolate affected systems
2. **Alert**: Notify security team and management
3. **Document**: Preserve logs and evidence
4. **Investigate**: Determine scope and impact
5. **Remediate**: Apply fixes and security patches
6. **Monitor**: Enhanced monitoring post-incident

#### **Data Loss Response**
1. **Stop**: Halt all operations to prevent further damage
2. **Assess**: Determine extent of data loss
3. **Restore**: From most recent verified backup
4. **Verify**: Data integrity and completeness
5. **Resume**: Operations with enhanced monitoring

---

## 📚 **Runbooks and Quick References**

### **Common Commands Quick Reference**

```bash
# Health Check
curl http://localhost:8088/health | jq

# Performance Metrics
curl http://localhost:8088/metrics | jq

# Test Proof Request
curl -X POST http://localhost:8088/prove -H "Content-Type: application/json" -d '{"goal": "BOX(A -> A)"}'

# Restart Service
docker-compose restart pxl-prover

# View Logs
tail -f logs/pxl-server.log

# Check Resource Usage
docker stats --no-stream

# Scale Session Pool
export PXL_POOL_SIZE=15 && docker-compose restart pxl-prover

# Rotate Logs
./scripts/rotate_logs.sh

# Run Integration Tests
python integration_test_suite.py

# Backup Configuration
./scripts/backup_config.sh

# Monitor Performance
watch -n 30 'curl -s http://localhost:8088/metrics | jq ".logos_pxl_p95_latency_ms"'
```

### **Environment Variables Reference**

```bash
# Core Configuration
ENABLE_HMAC_AUTH=true|false
HMAC_SECRET_KEY=<256-bit-hex-key>
PXL_SERVER_PORT=8088
PXL_POOL_SIZE=5
PXL_CACHE_TTL=300

# Performance Tuning
LOG_LEVEL=INFO|DEBUG|WARN|ERROR
MAX_REQUEST_SIZE=1048576
CONNECTION_TIMEOUT=60

# Security
RATE_LIMIT_ENABLED=true|false
RATE_LIMIT_PER_MINUTE=60
```

---

**End of Operations Manual**

*This manual provides comprehensive operational procedures for maintaining LOGOS_PXL_Core v0.5 in production environments with 99.9% uptime and optimal performance.*
