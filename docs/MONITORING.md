# Runtime Monitoring & Alerting Configuration

## Overview
Comprehensive monitoring for the LOGOS PXL Core verified runtime with automated alerting and SLO tracking.

## Service Level Objectives (SLOs)

### Availability SLO
- **Target**: 99.9% uptime (8.77 hours downtime per year)
- **Measurement**: Container health check success rate
- **Alert**: > 0.1% error rate over 5 minutes

### Latency SLO
- **Target**: 99% of requests < 150ms
- **Measurement**: Response time percentiles
- **Alert**: > 150ms p99 over 5 minutes

### Error Rate SLO
- **Target**: < 0.1% error rate
- **Measurement**: HTTP 5xx responses
- **Alert**: > 0.1% error rate over 5 minutes

## Health Check Endpoints

### /health
- **Purpose**: Basic service availability
- **Expected Response**: HTTP 200 with JSON status
- **Required Headers**:
  - `X-PXL-Coqchk: 8.20.1`
  - `X-Build-SHA: 1e77525`
  - `X-Release-Tag: v3.0.0-verified`

### /proof/ping
- **Purpose**: Verify verified core is loaded
- **Expected Response**: HTTP 200 with proof confirmation
- **Validation**: Response contains "verified_core_loaded"

## Monitoring Configuration

### Container Metrics
```yaml
# docker-compose.monitoring.yml
services:
  prometheus:
    image: prom/prometheus
    volumes:
      - ./monitoring/prometheus.yml:/etc/prometheus/prometheus.yml

  grafana:
    image: grafana/grafana
    environment:
      - GF_SECURITY_ADMIN_PASSWORD=changeme

  alertmanager:
    image: prom/alertmanager
    volumes:
      - ./monitoring/alertmanager.yml:/etc/alertmanager/alertmanager.yml
```

### Application Metrics
- **Request Count**: Total requests by endpoint
- **Response Time**: Histogram by endpoint
- **Error Count**: Errors by type and endpoint
- **Provenance Checks**: Header validation success rate

## Alerting Rules

### Critical Alerts (Page Immediately)
1. **Service Down**: Health check fails for 5+ minutes
2. **High Error Rate**: > 1% errors for 5 minutes
3. **Provenance Failure**: Missing or invalid verification headers
4. **Security Breach**: Unauthorized access attempts

### Warning Alerts (Investigate)
1. **High Latency**: p99 > 200ms for 5 minutes
2. **Resource Usage**: CPU/Memory > 90% for 10 minutes
3. **Log Errors**: Increased error log volume

### Info Alerts (Monitor)
1. **Deployment**: New version deployed
2. **Load Increase**: Request rate > 2x baseline
3. **Backup Status**: Backup job completion/failure

## Log Aggregation

### Application Logs
```yaml
# Collect logs from container
logging:
  driver: "json-file"
  options:
    max-size: "10m"
    max-file: "5"
    labels: "org.logos.component,org.logos.verified"
```

### Structured Logging
- **Format**: JSON with consistent fields
- **Required Fields**:
  - `timestamp`: ISO 8601
  - `level`: ERROR, WARN, INFO, DEBUG
  - `component`: pxl-core, gateway, etc.
  - `request_id`: Correlation ID
  - `message`: Human readable
  - `provenance`: Build SHA and verification status

## Dashboard Configuration

### Grafana Dashboards
1. **Service Overview**: Availability, latency, error rates
2. **Provenance Dashboard**: Verification status, build info
3. **Security Dashboard**: Failed auth, suspicious activity
4. **Performance Dashboard**: Resource usage, request patterns

### Key Metrics to Monitor
- Container restart count
- Health check success rate
- Average response time by endpoint
- Error rate by response code
- Resource usage (CPU, memory, network)
- Log volume and error patterns

## Automated Responses

### Self-Healing Actions
1. **Container Restart**: On health check failure
2. **Load Shedding**: Rate limiting when overloaded
3. **Circuit Breaker**: Stop requests to failing dependencies

### Escalation Procedures
1. **Level 1**: Automatic restart (5 minutes)
2. **Level 2**: Alert on-call engineer (15 minutes)
3. **Level 3**: Alert management team (1 hour)
4. **Level 4**: Alert executive team (4 hours)

## Testing & Validation

### Synthetic Monitoring
- **Health Check**: Every 30 seconds from multiple regions
- **Load Test**: Weekly automated k6 tests
- **Chaos Engineering**: Monthly failure injection tests

### Alert Validation
- **False Positive Rate**: < 1% of alerts
- **Mean Time to Detection**: < 5 minutes
- **Mean Time to Resolution**: < 30 minutes for critical issues