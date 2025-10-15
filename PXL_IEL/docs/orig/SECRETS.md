# Secrets Management Configuration

## Overview
Secure management of secrets and sensitive configuration for the LOGOS PXL Core verified runtime.

## Secret Types

### Runtime Secrets
- **JWT Signing Keys**: For authentication tokens
- **Database Credentials**: If persistent storage is added
- **API Keys**: For external service integrations
- **TLS Certificates**: For encrypted communications

### Build Secrets
- **Container Registry Credentials**: For image push/pull
- **Code Signing Keys**: For artifact signing
- **CI/CD Tokens**: For automated deployments

## Storage Strategy

### Primary: Vault
```hcl
# vault configuration
path "logos/pxl-core/*" {
  capabilities = ["read"]
}

# Runtime secrets
path "logos/pxl-core/runtime/*" {
  capabilities = ["read"]
}

# Build secrets
path "logos/pxl-core/build/*" {
  capabilities = ["read"]
}
```

### Secondary: Environment Variables (Ephemeral)
- Loaded at container startup
- Never persisted in images
- Rotated on each deployment

## Rotation Policy

### Automatic Rotation
- **JWT Keys**: Daily rotation
- **API Keys**: Weekly rotation
- **TLS Certificates**: Monthly rotation
- **Database Credentials**: On deployment

### Manual Rotation Triggers
- Security incident
- Key compromise suspicion
- Personnel changes
- Regulatory requirements

## Access Control

### Principle of Least Privilege
- Runtime containers: Read-only access to required secrets
- CI/CD pipelines: Time-limited access tokens
- Developers: No direct secret access

### Audit Logging
- All secret access logged
- Alerts on anomalous access patterns
- Regular audit reviews

## Implementation

### Container Secrets
```yaml
# docker-compose.secrets.yml
services:
  pxl-core:
    secrets:
      - jwt_private_key
      - api_keys
    environment:
      - JWT_KEY_FILE=/run/secrets/jwt_private_key
      - API_KEYS_FILE=/run/secrets/api_keys

secrets:
  jwt_private_key:
    external: true
  api_keys:
    external: true
```

### CI/CD Secrets
```yaml
# .github/workflows/deploy.yml
env:
  REGISTRY_TOKEN: ${{ secrets.REGISTRY_TOKEN }}
  COSIGN_PRIVATE_KEY: ${{ secrets.COSIGN_PRIVATE_KEY }}
  VAULT_TOKEN: ${{ secrets.VAULT_TOKEN }}
```

## Validation Checks

### Pre-Deployment
```bash
#!/bin/bash
# Check secrets are available
vault kv get logos/pxl-core/runtime/jwt-key > /dev/null
vault kv get logos/pxl-core/build/registry-token > /dev/null

# Validate secret formats
# JWT key should be valid PEM
# API keys should match expected format
```

### Runtime Validation
- Secrets loaded successfully on startup
- No secrets in logs or error messages
- Secret access audited and monitored

## Emergency Procedures

### Secret Compromise
1. **Immediate**: Rotate compromised secret
2. **Assessment**: Determine exposure scope
3. **Notification**: Alert affected parties
4. **Recovery**: Redeploy with new secrets

### Lost Access
1. **Escalation**: Contact security team
2. **Verification**: Confirm identity and authorization
3. **Recovery**: Restore access with audit trail

## Testing

### Secret Management Tests
- Secrets loaded correctly in test environment
- Rotation procedures work without downtime
- Access controls prevent unauthorized access
- Audit logs capture all access

### Integration Tests
- Application functions with rotated secrets
- No secrets leaked in logs or responses
- Performance impact of secret operations
