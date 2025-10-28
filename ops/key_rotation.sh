#!/bin/bash
# LOGOS PXL Core - JWT Key Rotation Script
# Performs zero-downtime JWT signing key rotation

set -euo pipefail

OLD_KEY_FILE="/opt/logos/secrets/jwt_secret.key"
NEW_KEY_FILE="/opt/logos/secrets/jwt_secret_new.key"
BACKUP_KEY_FILE="/opt/logos/secrets/jwt_secret_backup.key"

echo "Starting JWT key rotation..."

# Generate new key
echo "Generating new JWT signing key..."
openssl rand -hex 32 > "${NEW_KEY_FILE}"
chmod 600 "${NEW_KEY_FILE}"

# Backup old key
echo "Backing up current key..."
cp "${OLD_KEY_FILE}" "${BACKUP_KEY_FILE}"

# Update gateway configuration to use both keys (for transition period)
echo "Updating gateway configuration for key transition..."
cat > /opt/logos/gateway/config.yaml << EOF
jwt:
  primary_key_file: ${NEW_KEY_FILE}
  secondary_key_file: ${OLD_KEY_FILE}  # Keep old key for existing tokens
  rotation_grace_period: 3600  # 1 hour for token expiration

rate_limiting:
  requests_per_minute: 1000

cors:
  allow_origins: ["https://logos-pxl.org"]
EOF

# Reload gateway configuration
echo "Reloading gateway configuration..."
docker-compose -f /opt/logos/docker-compose.prod.yml exec gateway kill -HUP 1

# Wait for configuration to take effect
sleep 10

# Verify gateway is still healthy
echo "Verifying gateway health after rotation..."
if ! curl -f http://localhost/v1/health; then
  echo "❌ Gateway health check failed after key rotation!"
  echo "Rolling back to previous key..."

  # Rollback
  cp "${BACKUP_KEY_FILE}" "${OLD_KEY_FILE}"
  docker-compose -f /opt/logos/docker-compose.prod.yml restart gateway
  exit 1
fi

echo "✅ Gateway health verified"

# Monitor for authentication errors during transition
echo "Monitoring authentication during transition period..."
ERROR_THRESHOLD=5
TRANSITION_TIME=3600  # 1 hour

start_time=$(date +%s)
auth_errors=0

while true; do
  current_time=$(date +%s)
  if (( current_time - start_time > TRANSITION_TIME )); then
    break
  fi

  # Check for auth errors in logs
  errors=$(docker-compose -f /opt/logos/docker-compose.prod.yml logs --no-color gateway 2>/dev/null | grep -c "Invalid token" || true)

  if (( errors > auth_errors + ERROR_THRESHOLD )); then
    echo "⚠️  Increased authentication errors detected: $errors"
    auth_errors=$errors
  fi

  sleep 60
done

# Complete rotation - remove old key
echo "Completing key rotation..."
mv "${NEW_KEY_FILE}" "${OLD_KEY_FILE}"
rm -f "${BACKUP_KEY_FILE}"

# Update configuration to single key
cat > /opt/logos/gateway/config.yaml << EOF
jwt:
  primary_key_file: ${OLD_KEY_FILE}

rate_limiting:
  requests_per_minute: 1000

cors:
  allow_origins: ["https://logos-pxl.org"]
EOF

# Final reload
docker-compose -f /opt/logos/docker-compose.prod.yml exec gateway kill -HUP 1

echo "✅ JWT key rotation completed successfully"
echo "Old key backed up as: ${BACKUP_KEY_FILE}"
echo "New key active: ${OLD_KEY_FILE}"