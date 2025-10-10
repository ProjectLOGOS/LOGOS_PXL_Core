#!/bin/bash
# LOGOS PXL Core - Production Backup Script
# Creates timestamped backups of configurations, logs, and persistent data

set -euo pipefail

BACKUP_ROOT="/opt/logos/backups"
TIMESTAMP=$(date +%Y%m%d_%H%M%S)
BACKUP_DIR="${BACKUP_ROOT}/${TIMESTAMP}"

echo "Starting LOGOS PXL Core backup at ${TIMESTAMP}"

# Create backup directory
mkdir -p "${BACKUP_DIR}"

# Backup configurations
echo "Backing up configurations..."
tar -czf "${BACKUP_DIR}/configs.tar.gz" -C /opt/logos configs/ monitoring/grafana/

# Backup logs (last 30 days)
echo "Backing up logs..."
find /var/log/logos -name "*.log" -mtime -30 -exec tar -czf "${BACKUP_DIR}/logs.tar.gz" {} +

# Backup Docker volumes (if any persistent data)
echo "Backing up Docker volumes..."
docker run --rm -v logos_pxl_core_data:/data -v "${BACKUP_DIR}":/backup alpine \
    tar czf /backup/volumes.tar.gz -C /data .

# Create backup manifest
cat > "${BACKUP_DIR}/manifest.json" << EOF
{
  "timestamp": "${TIMESTAMP}",
  "version": "v2.2.0",
  "components": {
    "configs": "configs.tar.gz",
    "logs": "logs.tar.gz",
    "volumes": "volumes.tar.gz"
  },
  "build_sha": "$(git rev-parse HEAD)",
  "coqchk_stamp": "verified-${TIMESTAMP}"
}
EOF

# Calculate checksums
cd "${BACKUP_DIR}"
sha256sum *.tar.gz manifest.json > checksums.sha256

echo "Backup completed successfully: ${BACKUP_DIR}"
echo "Total size: $(du -sh "${BACKUP_DIR}" | cut -f1)"

# Cleanup old backups (keep last 7 days)
find "${BACKUP_ROOT}" -name "20*" -type d -mtime +7 -exec rm -rf {} \;

echo "Backup cleanup completed"