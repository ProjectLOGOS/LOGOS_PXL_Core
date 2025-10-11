# Disaster Recovery Configuration for LOGOS PXL Core

## Overview
This document outlines the disaster recovery (DR) and backup procedures for the LOGOS PXL Core verified runtime.

## Recovery Objectives

### Recovery Time Objective (RTO)
- **Critical**: 1 hour for core services
- **Important**: 4 hours for full system
- **Acceptable**: 24 hours for development environment

### Recovery Point Objective (RPO)
- **Verified Core**: 0 data loss (stateless)
- **Configuration**: 1 hour maximum data loss
- **Logs**: 15 minutes maximum data loss

## Backup Strategy

### Automated Backups
- **Frequency**: Every 6 hours
- **Retention**: 30 days for daily, 90 days for weekly
- **Storage**: Encrypted offsite location
- **Verification**: Automated integrity checks

### Components to Backup
1. **Container Images**: Signed and attested images in registry
2. **Configuration**: docker-compose.yml, environment files
3. **Secrets**: Encrypted in vault (not in backups)
4. **Logs**: Application and system logs
5. **SBOM**: Software bill of materials

## Recovery Procedures

### Scenario 1: Container Failure (Most Common)
```bash
# Quick recovery - restart container
docker compose -f docker-compose.verified.yml restart pxl-core

# Verify health
curl -f http://localhost:8080/health
```

### Scenario 2: Node Failure
```bash
# Full system recovery
./deploy-verified-core.sh

# Verify all components
docker compose -f docker-compose.verified.yml ps
curl -f http://localhost:8080/health
curl -f http://localhost:8080/proof/ping
```

### Scenario 3: Data Corruption
```bash
# Restore from backup
# 1. Stop services
docker compose -f docker-compose.verified.yml down

# 2. Restore configuration from backup
# 3. Redeploy
./deploy-verified-core.sh

# 4. Verify integrity
./scripts/security-scan.sh
```

## Monitoring & Alerting

### Health Checks
- Container health endpoint: `/health`
- Proof verification: `/proof/ping`
- Response time < 150ms (99th percentile)

### Alert Conditions
- Service unavailable > 5 minutes
- Health check fails > 3 times
- Provenance headers missing/invalid
- High error rate > 5%
- Resource usage > 90%

### Automated Recovery
- Container restart on health failure
- Service redeployment on persistent failure
- Alert escalation after 15 minutes

## Testing

### Quarterly DR Tests
1. **Failover Test**: Stop primary service, verify recovery
2. **Data Recovery Test**: Restore from backup, verify integrity
3. **Full System Test**: Complete rebuild from scratch

### Runbook Verification
- Document update after each test
- Measure actual RTO/RPO vs objectives
- Update contact lists and procedures

## Contacts

### Emergency Contacts
- **Primary**: Security Team (security@logos.foundation)
- **Secondary**: DevOps Team (devops@logos.foundation)
- **Vendor**: Container Registry Support

### Escalation
1. Alert primary contact
2. If no response in 30 minutes, escalate to secondary
3. If no response in 1 hour, escalate to vendor support