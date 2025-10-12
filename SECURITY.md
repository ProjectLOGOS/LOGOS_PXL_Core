# LOGOS PXL Core Security Guide

## Overview
This document outlines the security measures, threat model, and compliance requirements for LOGOS PXL Core production deployments.

## Threat Model

### Attack Vectors
1. **API Abuse**: Rate limiting bypass, authentication bypass
2. **Data Tampering**: Proof result manipulation, provenance spoofing
3. **Denial of Service**: Resource exhaustion, queue flooding
4. **Supply Chain**: Compromised dependencies, malicious builds
5. **Side Channels**: Timing attacks, information leakage

### Security Boundaries
- **External**: Internet-facing API gateway
- **Internal**: Service-to-service communication
- **Data**: Proof validation and cryptographic operations

## Authentication & Authorization

### JWT Implementation
- **Algorithm**: HS256 (HMAC-SHA256)
- **Key Management**: 256-bit secret, rotated quarterly
- **Token Lifetime**: 1 hour with automatic refresh
- **Claims**: Standard JWT claims + custom service permissions

### API Gateway Security
```python
# gateway/gateway.py - Key security features
from fastapi import Depends, HTTPException, status
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials
from slowapi import Limiter, _rate_limit_exceeded_handler
from slowapi.util import get_remote_address
from slowapi.errors import RateLimitExceeded

# Rate limiting
limiter = Limiter(key_func=get_remote_address)
app.state.limiter = limiter
app.add_exception_handler(RateLimitExceeded, _rate_limit_exceeded_handler)

# JWT validation
async def verify_token(credentials: HTTPAuthorizationCredentials = Depends(security)):
    try:
        payload = jwt.decode(credentials.credentials, SECRET_KEY, algorithms=["HS256"])
        return payload
    except JWTError:
        raise HTTPException(status_code=401, detail="Invalid token")
```

## Provenance & Integrity

### Build Provenance
- **Coq Verification**: All proofs verified with `coqchk`
- **Extraction Checksums**: SHA256 hashes of OCaml artifacts
- **Build Metadata**: Git commit SHAs, timestamps, build environment

### Response Headers
```http
X-PXL-Coqchk: verified
X-Build-SHA: a1b2c3d4...
X-V4-SHA: e5f6g7h8...
X-Request-ID: uuid-v4
```

### Integrity Verification
```bash
# Verify Coq extraction integrity
sha256sum extraction/*.ml > extraction.sha256
git add extraction.sha256

# CI/CD verification
coqchk -Q pxl-minimal-kernel-main/coq PXLs ...
```

## Network Security

### CORS Configuration
```yaml
# config/gateway.yaml
cors:
  allow_origins:
    - "https://trusted-domain.com"
    - "https://app.trusted-domain.com"
  allow_credentials: true
  allow_methods: ["GET", "POST", "OPTIONS"]
  allow_headers: ["Authorization", "Content-Type", "X-Requested-With"]
```

### Rate Limiting
- **Global**: 1000 requests/minute
- **Per-IP**: 100 requests/minute
- **Burst**: 50 requests
- **Endpoints**: Proof submission limited to 10/minute

### Service Isolation
- All services run in separate containers
- Network policies restrict inter-service communication
- No privileged containers
- Read-only root filesystems where possible

## Cryptographic Security

### Key Management
```bash
# Generate secure JWT secret
openssl rand -hex 32 > jwt_secret.key

# Environment variable (never in code)
export JWT_SECRET_KEY=$(cat jwt_secret.key)
```

### TLS Configuration
- **Minimum TLS**: 1.3
- **Cipher Suites**: ECDHE-RSA-AES256-GCM-SHA384
- **Certificate**: Let's Encrypt with automatic renewal
- **HSTS**: max-age=31536000; includeSubDomains

## Container Security

### Docker Security
```dockerfile
# deploy/Dockerfile.gateway
FROM python:3.11-slim

# Non-root user
RUN useradd --create-home --shell /bin/bash app
USER app

# Minimal attack surface
RUN apt-get update && apt-get install -y --no-install-recommends \
    curl \
    && rm -rf /var/lib/apt/lists/*

# No secrets in image
COPY --chown=app:app . /app
```

### Image Scanning
```yaml
# .github/workflows/production-pipeline.yml
- name: Run Trivy vulnerability scan
  uses: aquasecurity/trivy-action@master
  with:
    scan-type: 'image'
    scan-ref: 'logos-gateway:latest'
    format: 'sarif'
    output: 'trivy-results.sarif'
```

## Monitoring & Alerting

### Security Events
- Authentication failures
- Rate limit violations
- Unusual request patterns
- Provenance header anomalies

### Log Security
```python
# Structured logging with security context
import structlog

logger = structlog.get_logger()
logger.info("proof_validated",
    user_id=user_id,
    proof_id=proof_id,
    provenance_sha=provenance_sha,
    client_ip=request.client.host,
    user_agent=request.headers.get("User-Agent"))
```

### SIEM Integration
- Export logs to centralized SIEM
- Alert on security events
- Automated incident response

## Compliance

### Data Protection
- **GDPR**: Minimal data collection, proof results are ephemeral
- **CCPA**: No personal data stored beyond request logs
- **Data Retention**: Logs retained 30 days, metrics 90 days

### Audit Requirements
- **Access Logs**: All API requests logged with authentication context
- **Change Logs**: Code and configuration changes tracked
- **Security Events**: All security-related events logged and monitored

## Incident Response

### Breach Response
1. **Immediate**: Isolate affected systems
2. **Assessment**: Determine scope and impact
3. **Containment**: Block malicious activity
4. **Recovery**: Restore from clean backups
5. **Analysis**: Post-mortem and lessons learned

### Contact Information
- **Security Team**: security@logos-pxl.org
- **Emergency**: +1-555-0123 (24/7)
- **PGP Key**: Available at https://logos-pxl.org/security/pgp.asc

## Security Testing

### Penetration Testing
```bash
# API security testing
nuclei -t http-missing-security-headers -u http://localhost

# Container security
docker run --rm -v /var/run/docker.sock:/var/run/docker.sock
  goodwithtech/dockle:v0.4.14 logos-gateway:latest
```

### Dependency Scanning
```bash
# Python dependencies
safety check --full-report

# Container dependencies
trivy image logos-gateway:latest
```

## Security Updates

### Patch Management
- **Critical**: Apply within 24 hours
- **High**: Apply within 7 days
- **Medium**: Apply within 30 days
- **Low**: Apply during next maintenance window

### Vulnerability Disclosure
- **Responsible Disclosure**: security@logos-pxl.org
- **Timeline**: 90 days for fix development
- **Credits**: Public acknowledgment in release notes

## Hardening Checklist

### Pre-Deployment
- [ ] JWT secrets generated and stored securely
- [ ] CORS origins configured for production domains
- [ ] Rate limits tuned for expected load
- [ ] TLS certificates installed and valid
- [ ] Security headers configured
- [ ] Container images scanned for vulnerabilities
- [ ] Dependencies audited for known vulnerabilities

### Post-Deployment
- [ ] Security monitoring enabled
- [ ] Log aggregation configured
- [ ] Alert thresholds set
- [ ] Backup procedures tested
- [ ] Incident response plan documented
- [ ] Security team trained on procedures
