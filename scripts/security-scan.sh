#!/usr/bin/env bash
# security-scan.sh - Comprehensive security scanning for verified core

set -euo pipefail

IMAGE_NAME="${IMAGE_NAME:-logos-pxl-core:v3.0.0-verified}"
SBOM_FILE="${SBOM_FILE:-verified_slice_sbom.json}"

echo "🔒 Running comprehensive security scan for $IMAGE_NAME"

# Check if image exists
if ! docker image inspect "$IMAGE_NAME" &> /dev/null; then
    echo "❌ Image $IMAGE_NAME not found. Build it first."
    exit 1
fi

# Generate SBOM if not exists
if [ ! -f "$SBOM_FILE" ]; then
    if command -v syft &> /dev/null; then
        echo "📦 Generating SBOM..."
        syft packages . --output spdx-json="$SBOM_FILE"
        echo "✅ SBOM generated: $SBOM_FILE"
    else
        echo "⚠️  Syft not found - SBOM generation skipped"
    fi
fi

# Trivy vulnerability scan
if command -v trivy &> /dev/null; then
    echo "🔍 Running Trivy vulnerability scan..."
    trivy image --exit-code 1 --severity HIGH,CRITICAL "$IMAGE_NAME"

    echo "📊 Running Trivy security scan..."
    trivy image --exit-code 0 --format json "$IMAGE_NAME" > trivy-results.json
    echo "✅ Trivy scan completed: trivy-results.json"
else
    echo "⚠️  Trivy not found - vulnerability scan skipped"
fi

# Grype vulnerability scan
if command -v grype &> /dev/null; then
    echo "🔍 Running Grype vulnerability scan..."
    grype "$IMAGE_NAME" --fail-on high > grype-results.txt

    # Check for critical vulnerabilities
    if grep -q "Critical" grype-results.txt; then
        echo "❌ Critical vulnerabilities found in Grype scan"
        exit 1
    fi

    echo "✅ Grype scan completed: grype-results.txt"
else
    echo "⚠️  Grype not found - vulnerability scan skipped"
fi

# Cosign signing and attestation
if command -v cosign &> /dev/null; then
    echo "🔐 Signing container image..."

    # Sign the image
    cosign sign --yes "$IMAGE_NAME"
    echo "✅ Image signed"

    # Attest with SBOM if available
    if [ -f "$SBOM_FILE" ]; then
        cosign attest --predicate "$SBOM_FILE" --type spdx "$IMAGE_NAME"
        echo "✅ SBOM attestation added"
    fi

    # Verify signature
    cosign verify "$IMAGE_NAME"
    echo "✅ Signature verification passed"
else
    echo "⚠️  Cosign not found - image signing skipped"
fi

# Check for secrets in image
echo "🔑 Checking for secrets in container..."
if command -v trivy &> /dev/null; then
    trivy image --exit-code 0 --scanners secret "$IMAGE_NAME" > secrets-scan.txt

    if grep -q "Secret" secrets-scan.txt; then
        echo "❌ Secrets found in container image!"
        cat secrets-scan.txt
        exit 1
    fi

    echo "✅ No secrets found in container"
else
    echo "⚠️  Trivy not available - secrets scan skipped"
fi

# Check for secrets in git
echo "🔐 Checking for secrets in git repository..."
if command -v trivy &> /dev/null; then
    trivy fs --exit-code 0 --scanners secret . > git-secrets-scan.txt

    if grep -q "Secret" git-secrets-scan.txt; then
        echo "❌ Secrets found in git repository!"
        cat git-secrets-scan.txt
        exit 1
    fi

    echo "✅ No secrets found in git"
else
    echo "⚠️  Trivy not available - git secrets scan skipped"
fi

echo "🎉 Security scan completed successfully!"
echo "📄 Trivy results: trivy-results.json"
echo "📄 Grype results: grype-results.txt"
echo "📄 Secrets scan: secrets-scan.txt"
echo "📄 Git secrets: git-secrets-scan.txt"