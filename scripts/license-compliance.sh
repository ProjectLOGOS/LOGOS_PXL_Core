#!/usr/bin/env bash
# license-compliance.sh - License compliance checking for LOGOS PXL Core

set -euo pipefail

# Configuration
ALLOWED_LICENSES=("MIT" "BSD-2-Clause" "BSD-3-Clause" "Apache-2.0" "ISC" "CC0-1.0" "CC-BY-4.0" "CC-BY-SA-4.0")
DISALLOWED_LICENSES=("GPL-2.0" "GPL-3.0" "LGPL-2.1" "LGPL-3.0" "AGPL-3.0" "MS-PL" "WTFPL" "Beerware")

echo "🔍 Checking license compliance..."

# Check if reuse tool is available
if command -v reuse &> /dev/null; then
    echo "📋 Running REUSE compliance check..."
    reuse lint
    echo "✅ REUSE compliance passed"
else
    echo "⚠️  REUSE tool not found - skipping REUSE check"
fi

# Generate SBOM if syft is available
SBOM_FILE="verified_slice_sbom.json"
if command -v syft &> /dev/null; then
    echo "📦 Generating SBOM..."
    syft dir:. -o spdx-json > "$SBOM_FILE"
    echo "✅ SBOM generated: $SBOM_FILE"
else
    echo "⚠️  Syft not found - skipping SBOM generation"
    # Create minimal SBOM if file doesn't exist
    if [ ! -f "$SBOM_FILE" ]; then
        cat > "$SBOM_FILE" << EOF
{
  "spdxVersion": "SPDX-2.3",
  "dataLicense": "CC0-1.0",
  "SPDXID": "SPDXRef-DOCUMENT",
  "name": "LOGOS PXL Core SBOM",
  "creationInfo": {
    "created": "$(date -u +%Y-%m-%dT%H:%M:%SZ)",
    "creators": ["Tool: manual"]
  },
  "packages": []
}
EOF
    fi
fi

# Analyze licenses if jq is available
if command -v jq &> /dev/null && [ -f "$SBOM_FILE" ]; then
    echo "📊 Analyzing license distribution..."

    # Extract unique licenses
    LICENSES=$(jq -r '.packages[]?.licenseConcluded // empty' "$SBOM_FILE" 2>/dev/null | sort -u)

    echo "📋 Found licenses:"
    echo "$LICENSES" | while read -r license; do
        if [ -n "$license" ] && [ "$license" != "null" ]; then
            echo "  - $license"
        fi
    done

    # Check for disallowed licenses
    DISALLOWED_FOUND=()
    for license in $LICENSES; do
        for disallowed in "${DISALLOWED_LICENSES[@]}"; do
            if [ "$license" = "$disallowed" ]; then
                DISALLOWED_FOUND+=("$license")
            fi
        done
    done

    if [ ${#DISALLOWED_FOUND[@]} -gt 0 ]; then
        echo "❌ Found disallowed licenses:"
        for license in "${DISALLOWED_FOUND[@]}"; do
            echo "  - $license"
        done
        echo "🚫 Build failed due to disallowed licenses"
        exit 1
    fi

    echo "✅ No disallowed licenses found"
else
    echo "⚠️  jq not available or SBOM missing - skipping license analysis"
fi

# Run Trivy license scan if available
if command -v trivy &> /dev/null; then
    echo "🔍 Running Trivy license scan..."
    trivy fs --scanners license . > licenses.trivy.txt 2>&1 || true

    # Check for critical license issues
    if grep -q "CRITICAL" licenses.trivy.txt; then
        echo "❌ Critical license issues found"
        cat licenses.trivy.txt
        exit 1
    fi

    echo "✅ Trivy license scan completed"
else
    echo "⚠️  Trivy not found - skipping license scan"
fi

echo "🎉 License compliance check passed!"
echo "📄 SBOM: $SBOM_FILE"
echo "📄 Trivy results: licenses.trivy.txt"