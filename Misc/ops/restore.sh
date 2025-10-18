#!/bin/bash
# LOGOS PXL Core - Production Restore Script
# Restores from timestamped backups with integrity verification

set -euo pipefail

BACKUP_ROOT="/opt/logos/backups"
DRY_RUN=false

# Parse arguments
while [[ $# -gt 0 ]]; do
  case $1 in
    --dry-run)
      DRY_RUN=true
      shift
      ;;
    --backup-dir)
      BACKUP_DIR="$2"
      shift 2
      ;;
    *)
      echo "Usage: $0 [--dry-run] [--backup-dir <dir>]"
      exit 1
      ;;
  esac
done

# Find latest backup if not specified
if [[ -z "${BACKUP_DIR:-}" ]]; then
  BACKUP_DIR=$(find "${BACKUP_ROOT}" -name "20*" -type d | sort | tail -1)
fi

if [[ ! -d "${BACKUP_DIR}" ]]; then
  echo "Error: Backup directory not found: ${BACKUP_DIR}"
  exit 1
fi

echo "Starting LOGOS PXL Core restore from: ${BACKUP_DIR}"
if [[ "${DRY_RUN}" == "true" ]]; then
  echo "DRY RUN MODE - No changes will be made"
fi

# Verify backup integrity
echo "Verifying backup integrity..."
cd "${BACKUP_DIR}"
if ! sha256sum -c checksums.sha256; then
  echo "ERROR: Backup integrity check failed!"
  exit 1
fi

# Verify manifest
if ! jq -e '.timestamp and .version' manifest.json > /dev/null; then
  echo "ERROR: Invalid backup manifest!"
  exit 1
fi

echo "Backup integrity verified"

# Restore configurations
echo "Restoring configurations..."
if [[ "${DRY_RUN}" == "false" ]]; then
  tar -xzf configs.tar.gz -C /opt/logos
  echo "Configurations restored"
else
  echo "[DRY RUN] Would restore configurations from configs.tar.gz"
fi

# Restore logs
echo "Restoring logs..."
if [[ "${DRY_RUN}" == "false" ]]; then
  tar -xzf logs.tar.gz -C /var/log/logos
  echo "Logs restored"
else
  echo "[DRY RUN] Would restore logs from logs.tar.gz"
fi

# Restore volumes
echo "Restoring Docker volumes..."
if [[ "${DRY_RUN}" == "false" ]]; then
  docker run --rm -v logos_pxl_core_data:/data -v "${BACKUP_DIR}":/backup alpine \
      tar xzf /backup/volumes.tar.gz -C /data
  echo "Volumes restored"
else
  echo "[DRY RUN] Would restore volumes from volumes.tar.gz"
fi

# Post-restore validation
echo "Running post-restore validation..."
if [[ "${DRY_RUN}" == "false" ]]; then
  # Restart services to pick up restored configs
  docker-compose -f /opt/logos/docker-compose.prod.yml restart

  # Wait for services to be healthy
  sleep 30

  # Check health endpoints
  if curl -f http://localhost/v1/health; then
    echo "✅ Health check passed"
  else
    echo "❌ Health check failed"
    exit 1
  fi
else
  echo "[DRY RUN] Would restart services and validate health"
fi

echo "Restore completed successfully"
if [[ "${DRY_RUN}" == "true" ]]; then
  echo "Run without --dry-run to perform actual restore"
fi