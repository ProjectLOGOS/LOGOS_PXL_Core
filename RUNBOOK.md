# LOGOS PXL Core Production Runbook

## Overview
LOGOS PXL Core is a formal verification system providing mathematical proof validation through Coq-extracted OCaml overlays. This runbook covers deployment, monitoring, and troubleshooting for production operations.

## Architecture

### Core Components
- **PXL Core**: Coq-extracted OCaml kernel (port 8080)
- **Overlay Chrono**: Chronological proof validation (port 8081)
- **Overlay V4**: V4 compatibility layer (port 8082)
- **API Gateway**: FastAPI proxy with auth/rate limiting (port 80)
- **GUI**: React/TypeScript web interface (port 3000)
- **Monitoring**: Prometheus/Grafana stack (port 9090/3001)

### Data Flow
```
Client → Gateway → Overlay Services → PXL Core
    ↓         ↓         ↓         ↓
   JWT      Auth     Proof     Coqchk
   CORS    Rate     Validate  Verify
 Headers  Limit    Results   Proofs
```

## Deployment

### Prerequisites
- Docker Engine 24+
- Docker Compose v2.20+
- 8GB RAM minimum
- Ubuntu 22.04+ or equivalent

### Quick Start
```bash
# Clone repository
git clone https://github.com/your-org/logos-pxl-core.git
cd logos-pxl-core

# Deploy production stack
docker-compose -f docker-compose.prod.yml up -d

# Verify deployment
curl http://localhost/v1/health
```

### Environment Variables
```bash
# Gateway Configuration
JWT_SECRET_KEY=your-256-bit-secret
CORS_ORIGINS=https://your-domain.com
RATE_LIMIT_REQUESTS=100
RATE_LIMIT_WINDOW=60

# Monitoring
PROMETHEUS_RETENTION=30d
GRAFANA_ADMIN_PASSWORD=secure-password

# Services
PXL_CORE_PORT=8080
OVERLAY_CHRONO_PORT=8081
OVERLAY_V4_PORT=8082
```

## Monitoring

### Key Metrics
- **Proof Latency**: P95 < 300ms
- **Success Rate**: > 95%
- **Error Rate**: < 5%
- **Queue Depth**: < 10 requests

### Health Checks
```bash
# Individual services
curl http://localhost:8080/healthz  # PXL Core
curl http://localhost:8081/health   # Overlay Chrono
curl http://localhost:8082/health   # Overlay V4
curl http://localhost/v1/health     # Gateway

# GUI accessibility
curl http://localhost:3000
```

### Grafana Dashboards
Access at http://localhost:3001 with admin credentials.

## Troubleshooting

### Common Issues

#### High Latency
1. Check queue depth: `docker stats`
2. Monitor CPU/memory usage
3. Scale services if needed:
   ```bash
   docker-compose -f docker-compose.prod.yml up -d --scale overlay-chrono=2
   ```

#### Authentication Failures
1. Verify JWT_SECRET_KEY consistency
2. Check token expiration (1 hour default)
3. Validate CORS origins configuration

#### Proof Validation Errors
1. Check Coq extraction artifacts
2. Verify overlay service logs:
   ```bash
   docker-compose logs overlay-chrono
   ```
3. Validate input format against OpenAPI spec

#### Memory Issues
1. Monitor container memory usage
2. Adjust Docker memory limits in compose file
3. Consider horizontal scaling for high load

### Log Analysis
```bash
# View all service logs
docker-compose logs -f

# Filter by service
docker-compose logs gateway | grep ERROR

# Export logs for analysis
docker-compose logs > production-logs.txt
```

## Backup and Recovery

### Data Backup
```bash
# Backup configurations
tar -czf config-backup.tar.gz configs/ monitoring/grafana/

# Backup Docker volumes (if any)
docker run --rm -v logos_pxl_core_data:/data -v $(pwd):/backup alpine tar czf /backup/data-backup.tar.gz -C /data .
```

### Recovery Procedures
1. Stop services: `docker-compose down`
2. Restore configurations
3. Start services: `docker-compose up -d`
4. Verify health checks pass

## Scaling

### Horizontal Scaling
```yaml
# docker-compose.prod.yml
services:
  overlay-chrono:
    deploy:
      replicas: 3
    labels:
      - "traefik.http.services.overlay-chrono.loadbalancer.server.port=8080"
```

### Vertical Scaling
- PXL Core: 2-4 CPU cores, 4GB RAM
- Overlays: 1-2 CPU cores, 2GB RAM each
- Gateway: 2 CPU cores, 2GB RAM
- GUI: 1 CPU core, 1GB RAM

## Security

### Network Security
- All services behind API gateway
- Rate limiting: 100 requests/minute
- CORS configured for allowed origins
- No direct external access to core services

### Authentication
- JWT tokens with HS256 signing
- 1-hour token expiration
- Automatic token refresh in GUI

### Provenance Headers
- X-PXL-Coqchk: Coq verification status
- X-Build-SHA: Build commit hash
- X-V4-SHA: V4 extraction hash

## Performance Tuning

### Gateway Configuration
```yaml
# config/gateway.yaml
rate_limiting:
  requests_per_minute: 1000
  burst_limit: 100

cors:
  allow_origins: ["https://trusted-domain.com"]
  allow_credentials: true
```

### Monitoring Thresholds
- Alert on: Error rate > 5%
- Alert on: P95 latency > 500ms
- Alert on: Queue depth > 20

## Maintenance

### Regular Tasks
- Weekly: Review Grafana dashboards
- Monthly: Update Docker images
- Quarterly: Security audit and dependency updates

### Updates
```bash
# Update to latest version
git pull origin main
docker-compose build --no-cache
docker-compose up -d
```

### Emergency Procedures
1. Immediate: Check service health
2. If degraded: Scale up resources
3. If critical: Rollback to previous version
4. Post-mortem: Analyze logs and metrics