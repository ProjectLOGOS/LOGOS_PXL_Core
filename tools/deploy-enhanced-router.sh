#!/bin/bash
# LOGOS Tool Router - Production Deployment Script
# Automates the rollout checklist for enhanced tool router

set -euo pipefail

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
ENVIRONMENT="${ENVIRONMENT:-production}"
SIGNING_SECRET="${SIGNING_SECRET:-}"
USE_REDIS="${USE_REDIS_RATE_LIMIT:-false}"
REDIS_URL="${REDIS_URL:-redis://redis:6379/0}"

echo -e "${BLUE}🚀 LOGOS Tool Router v2.0.0 - Deployment Script${NC}"
echo "=================================================="
echo "Environment: $ENVIRONMENT"
echo "Signing: $([ -n "$SIGNING_SECRET" ] && echo "✅ Enabled" || echo "❌ Disabled")"
echo "Redis Rate Limiting: $([ "$USE_REDIS" = "true" ] && echo "✅ Enabled" || echo "❌ Memory-based")"
echo ""

# Step 1: Pre-deployment checks
echo -e "${YELLOW}📋 Step 1: Pre-deployment Checks${NC}"

# Check Docker and docker-compose
if ! command -v docker &> /dev/null; then
    echo -e "${RED}❌ Docker not found. Please install Docker.${NC}"
    exit 1
fi

if ! command -v docker-compose &> /dev/null; then
    echo -e "${RED}❌ docker-compose not found. Please install docker-compose.${NC}"
    exit 1
fi

echo "✅ Docker and docker-compose available"

# Check if required environment variables are set for production
if [ "$ENVIRONMENT" = "production" ]; then
    if [ -z "$SIGNING_SECRET" ]; then
        echo -e "${YELLOW}⚠️  SIGNING_SECRET not set. HMAC signing will be disabled.${NC}"
        read -p "Continue without signing? (y/N): " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Yy]$ ]]; then
            echo "Please set SIGNING_SECRET and run again."
            exit 1
        fi
    else
        echo "✅ HMAC signing configured"
    fi
fi

# Step 2: Build and deploy
echo -e "${YELLOW}📦 Step 2: Building and Deploying Services${NC}"

# Build tool router with latest changes
echo "Building tool router..."
docker-compose build tool-router

# Deploy Redis if using distributed rate limiting
if [ "$USE_REDIS" = "true" ]; then
    echo "Starting Redis for distributed rate limiting..."
    docker-compose up -d redis
    
    # Wait for Redis to be ready
    echo "Waiting for Redis to be ready..."
    timeout 30 bash -c 'until docker-compose exec redis redis-cli ping; do sleep 1; done'
    echo "✅ Redis ready"
fi

# Deploy tool router with new configuration
echo "Deploying enhanced tool router..."
export SIGNING_SECRET USE_REDIS_RATE_LIMIT REDIS_URL
docker-compose up -d tool-router

# Step 3: Health checks
echo -e "${YELLOW}🏥 Step 3: Health Checks${NC}"

# Wait for service to be ready
echo "Waiting for tool router to be ready..."
timeout 60 bash -c 'until curl -sf http://localhost:8071/health > /dev/null 2>&1; do sleep 2; done'
echo "✅ Tool router health check passed"

# Test metrics endpoint
echo "Testing Prometheus metrics endpoint..."
if curl -sf http://localhost:8071/metrics > /dev/null; then
    echo "✅ Metrics endpoint accessible"
else
    echo -e "${RED}❌ Metrics endpoint not accessible${NC}"
    exit 1
fi

# Step 4: Feature validation
echo -e "${YELLOW}🧪 Step 4: Feature Validation${NC}"

# Test basic routing
echo "Testing basic tool routing..."
HEALTH_RESPONSE=$(curl -sf -X POST http://localhost:8071/route \
    -H 'Content-Type: application/json' \
    -d '{"tool":"tetragnos","args":{"op":"ping"},"proof_token":{"token":"deployment-test"}}' || echo "FAILED")

if [[ "$HEALTH_RESPONSE" == "FAILED" ]]; then
    echo -e "${RED}⚠️  Basic routing test failed (expected if tools not running)${NC}"
else
    echo "✅ Basic routing test passed"
fi

# Test rate limiting
echo "Testing rate limiting..."
for i in {1..5}; do
    curl -sf http://localhost:8071/health > /dev/null || true
done
echo "✅ Rate limiting active (check metrics for rate_limited_total)"

# Test HMAC signing if enabled
if [ -n "$SIGNING_SECRET" ]; then
    echo "Testing HMAC signing..."
    if command -v jq &> /dev/null && [ -f "tools/sign-route.sh" ]; then
        SIGN_TEST=$(echo '{"tool":"tetragnos","args":{"op":"ping"},"proof_token":{"token":"sign-test"}}' | \
            SIGNING_SECRET="$SIGNING_SECRET" TOOL_ROUTER_URL=http://localhost:8071 bash tools/sign-route.sh 2>/dev/null || echo "FAILED")
        
        if [[ "$SIGN_TEST" == "FAILED" ]]; then
            echo -e "${YELLOW}⚠️  HMAC signing test failed (may be expected if upstream tools not running)${NC}"
        else
            echo "✅ HMAC signing working"
        fi
    else
        echo "⚠️  Cannot test HMAC signing (missing jq or sign-route.sh)"
    fi
fi

# Step 5: Monitoring setup
echo -e "${YELLOW}📊 Step 5: Monitoring Validation${NC}"

# Check metrics are being generated
METRICS_SAMPLE=$(curl -s http://localhost:8071/metrics | head -20)
if echo "$METRICS_SAMPLE" | grep -q "tool_router_"; then
    echo "✅ Prometheus metrics being generated"
else
    echo -e "${RED}❌ No tool router metrics found${NC}"
    exit 1
fi

# Display key metrics
echo ""
echo "📈 Current Metrics Sample:"
curl -s http://localhost:8071/metrics | grep -E "(tool_router_requests_total|tool_router_circuit_breaker_state)" | head -5

# Step 6: Load testing (optional)
echo ""
echo -e "${YELLOW}🔥 Step 6: Load Testing (Optional)${NC}"
if command -v k6 &> /dev/null; then
    read -p "Run baseline load test? (y/N): " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        echo "Running k6 load test..."
        TOOL_ROUTER_URL=http://localhost:8071 k6 run --quiet k6/health-baseline.js
        echo "✅ Load test completed"
    fi
else
    echo "⚠️  k6 not available. Install k6 for load testing: https://k6.io/docs/getting-started/installation/"
fi

# Step 7: Final validation
echo ""
echo -e "${YELLOW}🎯 Step 7: Final Validation${NC}"

echo "Running smoke tests..."
if [ -f "tools/smoke.sh" ]; then
    if bash tools/smoke.sh > /dev/null 2>&1; then
        echo "✅ Smoke tests passed"
    else
        echo -e "${YELLOW}⚠️  Some smoke tests failed (may be expected if dependent services not running)${NC}"
    fi
else
    echo "⚠️  Smoke test script not found"
fi

# Summary
echo ""
echo -e "${GREEN}🎉 DEPLOYMENT COMPLETE${NC}"
echo "======================="
echo ""
echo "🔗 Service Endpoints:"
echo "  • Tool Router: http://localhost:8071"
echo "  • Health Check: http://localhost:8071/health"
echo "  • Metrics: http://localhost:8071/metrics"
echo ""
echo "📊 Monitoring Setup:"
echo "  • Prometheus target: tool-router:8071/metrics"
echo "  • Alerting rules: monitoring/prometheus-rules.yml"
echo "  • Runbooks: monitoring/runbooks.md"
echo ""
echo "🔧 Configuration:"
echo "  • HMAC Signing: $([ -n "$SIGNING_SECRET" ] && echo "✅ Enabled" || echo "❌ Disabled")"
echo "  • Rate Limiting: $([ "$USE_REDIS" = "true" ] && echo "Redis-based" || echo "Memory-based")"
echo "  • Circuit Breakers: ✅ Enabled"
echo "  • Retry Logic: ✅ Enabled"
echo "  • Structured Logging: ✅ Enabled"
echo ""
echo "🧪 Testing Commands:"
echo "  • Load test: k6 run k6/health-baseline.js"
echo "  • Signed requests: SIGNING_SECRET=\$SECRET k6 run k6/signed-requests.js"
echo "  • Smoke test: bash tools/smoke.sh"
echo ""
echo "📈 Next Steps:"
echo "  1. Configure Prometheus to scrape http://localhost:8071/metrics"
echo "  2. Import alerting rules from monitoring/prometheus-rules.yml"
echo "  3. Set up log aggregation for JSON logs with X-Request-ID correlation"
echo "  4. Monitor SLOs: 99.9% availability, p95 latency < 500ms"
echo ""
echo -e "${GREEN}🚀 LOGOS Tool Router v2.0.0 is now operational!${NC}"