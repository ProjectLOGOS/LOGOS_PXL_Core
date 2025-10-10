# LOGOS PXL Core Operations Guide

## Service Level Objectives (SLOs)

### Availability
- **Target**: 99.9% uptime (8.77 hours downtime/year)
- **Measurement**: Successful health check responses
- **Alert Threshold**: < 99.5% over 5-minute windows

### Performance
- **Proof Latency**: P95 < 300ms, P99 < 500ms
- **Success Rate**: > 95% of valid requests
- **Error Rate**: < 5% of all requests
- **Queue Depth**: < 10 pending requests

### Reliability
- **MTTR**: < 15 minutes for service degradation
- **MTTD**: < 5 minutes for incident detection
- **Recovery Time**: < 30 minutes for full restoration

## Monitoring Dashboard

### Key Metrics to Monitor

#### System Health
```
✅ Gateway: http://localhost/v1/health
✅ PXL Core: http://localhost:8080/healthz
✅ Overlay Chrono: http://localhost:8081/health
✅ Overlay V4: http://localhost:8082/health
✅ GUI: http://localhost:3000
```

#### Performance Metrics
- **Request Rate**: requests/second across all endpoints
- **Latency Distribution**: P50, P95, P99 response times
- **Error Rate**: 4xx/5xx responses as percentage
- **Queue Depth**: Pending requests in processing queue

#### Resource Usage
- **CPU Usage**: Per service container
- **Memory Usage**: RSS and virtual memory
- **Disk I/O**: Read/write operations
- **Network I/O**: Bandwidth utilization

### Grafana Panels

#### Proof Performance Dashboard
```
Panel 1: Request Rate (requests/sec)
  Query: rate(http_requests_total[5m])

Panel 2: Latency Distribution
  Query: histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m]))

Panel 3: Error Rate (%)
  Query: rate(http_requests_total{status=~"5.."}[5m]) / rate(http_requests_total[5m]) * 100

Panel 4: Queue Depth
  Query: proof_queue_length
```

#### System Resources Dashboard
```
Panel 1: CPU Usage by Service
  Query: rate(container_cpu_usage_seconds_total[5m]) * 100

Panel 2: Memory Usage
  Query: container_memory_usage_bytes / container_spec_memory_limit_bytes * 100

Panel 3: Network I/O
  Query: rate(container_network_receive_bytes_total[5m])

Panel 4: Disk I/O
  Query: rate(container_fs_reads_bytes_total[5m])
```

## Alerting Rules

### Critical Alerts (Page immediately)
```yaml
# Prometheus alerting rules
groups:
  - name: pxl_core_critical
    rules:
      - alert: PXLCoreDown
        expr: up{job="pxl-core"} == 0
        for: 2m
        labels:
          severity: critical
        annotations:
          summary: "PXL Core service is down"
          description: "PXL Core has been down for more than 2 minutes"

      - alert: HighErrorRate
        expr: rate(http_requests_total{status=~"5.."}[5m]) / rate(http_requests_total[5m]) > 0.05
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "High error rate detected"
          description: "Error rate > 5% for 5 minutes"

      - alert: HighLatency
        expr: histogram_quantile(0.95, rate(http_request_duration_seconds_bucket[5m])) > 0.5
        for: 5m
        labels:
          severity: critical
        annotations:
          summary: "High latency detected"
          description: "P95 latency > 500ms for 5 minutes"
```

### Warning Alerts (Monitor closely)
```yaml
  - name: pxl_core_warning
    rules:
      - alert: QueueDepthHigh
        expr: proof_queue_length > 20
        for: 2m
        labels:
          severity: warning
        annotations:
          summary: "High queue depth"
          description: "Queue depth > 20 requests"

      - alert: ResourceUsageHigh
        expr: container_memory_usage_bytes / container_spec_memory_limit_bytes > 0.8
        for: 5m
        labels:
          severity: warning
        annotations:
          summary: "High memory usage"
          description: "Memory usage > 80% for 5 minutes"
```

## Incident Response

### Severity Levels

#### P0 - Critical (System Down)
- **Impact**: Complete service outage
- **Response**: Immediate page, all hands on deck
- **Target Resolution**: 30 minutes
- **Communication**: Immediate stakeholder notification

#### P1 - High (Degraded Performance)
- **Impact**: High latency or error rates
- **Response**: Page on-call engineer
- **Target Resolution**: 2 hours
- **Communication**: Update stakeholders hourly

#### P2 - Medium (Partial Degradation)
- **Impact**: Some features affected
- **Response**: Create ticket, assign to engineer
- **Target Resolution**: 8 hours
- **Communication**: Daily updates

#### P3 - Low (Minor Issues)
- **Impact**: Cosmetic or minor functionality
- **Response**: Create ticket for next sprint
- **Target Resolution**: 24 hours
- **Communication**: Weekly summary

### Response Process

#### 1. Detection
- Automated alerts trigger
- Monitoring dashboard shows anomalies
- User reports via support channels

#### 2. Assessment
```bash
# Quick health check
curl -f http://localhost/v1/health || echo "Gateway down"

# Check service logs
docker-compose logs --tail=100 gateway

# Check resource usage
docker stats
```

#### 3. Containment
```bash
# Scale up if needed
docker-compose up -d --scale overlay-chrono=3

# Restart failing service
docker-compose restart gateway

# Rollback if necessary
git checkout previous-stable-tag
docker-compose build --no-cache
docker-compose up -d
```

#### 4. Recovery
- Verify all health checks pass
- Monitor for 30 minutes
- Gradually reduce scaling if applied

#### 5. Post-Mortem
- Document root cause
- Update runbook with lessons learned
- Implement preventive measures

## Capacity Planning

### Current Limits
- **Concurrent Users**: 1000 active sessions
- **Request Rate**: 1000 requests/minute
- **Proof Complexity**: Up to 10MB input size
- **Storage**: 100GB logs/metrics retention

### Scaling Triggers
- CPU usage > 70% for 15 minutes
- Memory usage > 80% for 10 minutes
- Queue depth > 50 for 5 minutes
- P95 latency > 400ms for 10 minutes

### Scaling Strategies

#### Horizontal Scaling
```bash
# Scale overlay services
docker-compose up -d --scale overlay-chrono=5

# Add more gateway instances
docker-compose up -d --scale gateway=3
```

#### Vertical Scaling
```yaml
# docker-compose.prod.yml
services:
  pxl-core:
    deploy:
      resources:
        limits:
          cpus: '4.0'
          memory: 8G
        reservations:
          cpus: '2.0'
          memory: 4G
```

## Backup and Recovery

### Backup Schedule
- **Configurations**: Daily at 02:00 UTC
- **Logs**: Hourly rotation, 30-day retention
- **Metrics**: Continuous export to S3, 90-day retention
- **Code**: Git repository with all history

### Recovery Procedures

#### Configuration Recovery
```bash
# Restore from backup
tar -xzf config-backup-2024-01-15.tar.gz -C /

# Restart services
docker-compose down
docker-compose up -d
```

#### Data Recovery
```bash
# Restore from snapshot
docker run --rm -v logos_pxl_core_data:/data \
  -v $(pwd):/backup alpine \
  tar xzf /backup/data-backup.tar.gz -C /data

# Verify integrity
docker-compose exec pxl-core /app/verify-data-integrity.sh
```

### Disaster Recovery
1. **RTO**: 4 hours (time to restore service)
2. **RPO**: 1 hour (maximum data loss)
3. **Backup Location**: Multi-region S3 with cross-region replication
4. **Failover**: Automatic DNS failover to backup region

## Maintenance Windows

### Scheduled Maintenance
- **Weekly**: Sunday 02:00-04:00 UTC (2 hours)
  - Security patches
  - Log rotation
  - Certificate renewal

- **Monthly**: First Sunday 01:00-03:00 UTC (2 hours)
  - Major version updates
  - Database maintenance
  - Performance optimizations

### Emergency Maintenance
- Announced 24 hours in advance
- Limited to 4 hours maximum
- Rollback plan required
- Stakeholder communication mandatory

## Performance Optimization

### Profiling
```bash
# CPU profiling
docker-compose exec pxl-core py-spy top --pid $(pgrep -f pxl-core)

# Memory profiling
docker-compose exec overlay-chrono heaptrack /app/overlay-chrono
```

### Optimization Targets
- **Memory**: Reduce peak usage by 20%
- **CPU**: Improve throughput by 30%
- **Latency**: Reduce P95 by 100ms
- **Resource Usage**: Optimize container sizes

### Continuous Improvement
- Weekly performance reviews
- Monthly capacity planning sessions
- Quarterly architecture reviews
- Annual disaster recovery testing

## Compliance and Audit

### Audit Logs
- All API requests logged with:
  - Timestamp
  - User ID (if authenticated)
  - Request method and path
  - Response status code
  - Processing duration
  - Client IP and User-Agent

### Compliance Checks
- **GDPR**: Data minimization, right to erasure
- **SOX**: Financial controls (if applicable)
- **ISO 27001**: Information security management
- **SOC 2**: Trust services criteria

### Regular Audits
- **Internal**: Monthly security reviews
- **External**: Annual penetration testing
- **Compliance**: Quarterly regulatory audits
- **Performance**: Continuous monitoring and alerting