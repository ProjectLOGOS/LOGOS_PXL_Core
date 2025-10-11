#!/usr/bin/env bash
# deploy-verified-core.sh - Production deployment script for verified PXL core

set -euo pipefail

# Configuration
IMAGE_NAME="logos-pxl-core"
TAG="v3.0.0-verified"
BUILD_SHA="40360dc"
REGISTRY="${REGISTRY:-ghcr.io/projectlogos}"

echo "🚀 Deploying LOGOS PXL Core - Verified Slice"
echo "Build SHA: $BUILD_SHA"
echo "Release Tag: $TAG"
echo

# Step 1: Build OCaml runtime
echo "📦 Building OCaml runtime..."
if command -v opam &> /dev/null; then
    opam switch create pxl-verified ocaml-base-compiler.5.1.1 || true
    eval $(opam env)
    opam install -y dune cohttp-lwt-unix lwt yojson
    dune build
    echo "✅ OCaml build complete"
else
    echo "⚠️  Opam not found - skipping OCaml build (assuming pre-built)"
fi

# Step 2: Build container
echo "🐳 Building container image..."
docker build -t "$REGISTRY/$IMAGE_NAME:$TAG" -f Dockerfile.pxl-core .
docker tag "$REGISTRY/$IMAGE_NAME:$TAG" "$REGISTRY/$IMAGE_NAME:latest"
echo "✅ Container build complete"

# Step 3: Run security scan
echo "🔍 Running security scan..."
if command -v trivy &> /dev/null; then
    trivy image --exit-code 0 --no-progress "$REGISTRY/$IMAGE_NAME:$TAG"
    echo "✅ Security scan complete"
else
    echo "⚠️  Trivy not found - skipping security scan"
fi

# Step 4: Generate SBOM
echo "📋 Generating SBOM..."
if command -v syft &> /dev/null; then
    syft packages . --output spdx-json=verified_slice_sbom.json
    echo "✅ SBOM generated"
else
    echo "⚠️  Syft not found - skipping SBOM generation"
fi

# Step 5: Deploy with docker-compose
echo "🚀 Deploying verified core..."
docker compose -f docker-compose.verified.yml up -d pxl-core
echo "✅ Deployment complete"

# Step 6: Health checks
echo "🏥 Running health checks..."
sleep 10

HEALTH_STATUS=$(curl -s -o /dev/null -w "%{http_code}" http://localhost:8080/health)
if [ "$HEALTH_STATUS" -eq 200 ]; then
    echo "✅ Health check passed"

    # Check provenance headers
    BUILD_SHA_HEADER=$(curl -s -I http://localhost:8080/health | grep -i "x-build-sha" | awk '{print $2}' | tr -d '\r')
    RELEASE_TAG_HEADER=$(curl -s -I http://localhost:8080/health | grep -i "x-release-tag" | awk '{print $2}' | tr -d '\r')

    if [ "$BUILD_SHA_HEADER" = "$BUILD_SHA" ] && [ "$RELEASE_TAG_HEADER" = "$TAG" ]; then
        echo "✅ Provenance headers verified"
    else
        echo "❌ Provenance headers mismatch"
        exit 1
    fi
else
    echo "❌ Health check failed (status: $HEALTH_STATUS)"
    exit 1
fi

# Step 7: Run load test baseline
echo "⚡ Running load test baseline..."
if command -v k6 &> /dev/null; then
    k6 run k6/verified-core-baseline.js
    echo "✅ Load test complete"
else
    echo "⚠️  K6 not found - skipping load test"
fi

echo
echo "🎉 LOGOS PXL Core - Verified Slice deployment complete!"
echo "🌐 Health endpoint: http://localhost:8080/health"
echo "🔗 Proof endpoint: http://localhost:8080/proof/ping"
echo "📊 Build SHA: $BUILD_SHA"
echo "🏷️  Release Tag: $TAG"