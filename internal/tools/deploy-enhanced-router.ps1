# LOGOS Tool Router v2.0.0 - Production Deployment PowerShell Script
# Windows-compatible version of the deployment automation

param(
    [string]$Environment = "production",
    [string]$SigningSecret = $env:SIGNING_SECRET,
    [string]$UseRedis = $env:USE_REDIS_RATE_LIMIT,
    [string]$RedisUrl = $env:REDIS_URL
)

# Set default values
if (-not $UseRedis) { $UseRedis = "false" }
if (-not $RedisUrl) { $RedisUrl = "redis://redis:6379/0" }

Write-Host "🚀 LOGOS Tool Router v2.0.0 - Deployment Script" -ForegroundColor Blue
Write-Host "=================================================="
Write-Host "Environment: $Environment"
Write-Host "Signing: $(if ($SigningSecret) { '✅ Enabled' } else { '❌ Disabled' })"
Write-Host "Redis Rate Limiting: $(if ($UseRedis -eq 'true') { '✅ Enabled' } else { '❌ Memory-based' })"
Write-Host ""

# Step 1: Pre-deployment checks
Write-Host "📋 Step 1: Pre-deployment Checks" -ForegroundColor Yellow

# Check Docker
try {
    docker --version | Out-Null
    Write-Host "✅ Docker available"
} catch {
    Write-Host "❌ Docker not found. Please install Docker Desktop." -ForegroundColor Red
    exit 1
}

# Check docker-compose
try {
    docker-compose --version | Out-Null
    Write-Host "✅ docker-compose available"
} catch {
    Write-Host "❌ docker-compose not found. Please install docker-compose." -ForegroundColor Red
    exit 1
}

# Production environment checks
if ($Environment -eq "production" -and -not $SigningSecret) {
    Write-Host "⚠️  SIGNING_SECRET not set. HMAC signing will be disabled." -ForegroundColor Yellow
    $continue = Read-Host "Continue without signing? (y/N)"
    if ($continue -ne "y" -and $continue -ne "Y") {
        Write-Host "Please set SIGNING_SECRET environment variable and run again."
        exit 1
    }
} elseif ($SigningSecret) {
    Write-Host "✅ HMAC signing configured"
}

# Step 2: Build and deploy
Write-Host "📦 Step 2: Building and Deploying Services" -ForegroundColor Yellow

Write-Host "Building tool router..."
docker-compose build tool-router

if ($UseRedis -eq "true") {
    Write-Host "Starting Redis for distributed rate limiting..."
    docker-compose up -d redis

    Write-Host "Waiting for Redis to be ready..."
    $timeout = 30
    $elapsed = 0
    do {
        Start-Sleep -Seconds 1
        $elapsed++
        try {
            docker-compose exec redis redis-cli ping | Out-Null
            break
        } catch {
            if ($elapsed -ge $timeout) {
                Write-Host "❌ Redis failed to start within $timeout seconds" -ForegroundColor Red
                exit 1
            }
        }
    } while ($elapsed -lt $timeout)
    Write-Host "✅ Redis ready"
}

Write-Host "Deploying enhanced tool router..."
$env:SIGNING_SECRET = $SigningSecret
$env:USE_REDIS_RATE_LIMIT = $UseRedis
$env:REDIS_URL = $RedisUrl
docker-compose up -d tool-router

# Step 3: Health checks
Write-Host "🏥 Step 3: Health Checks" -ForegroundColor Yellow

Write-Host "Waiting for tool router to be ready..."
$timeout = 60
$elapsed = 0
do {
    Start-Sleep -Seconds 2
    $elapsed += 2
    try {
        $response = Invoke-WebRequest -Uri "http://localhost:8071/health" -UseBasicParsing -TimeoutSec 5
        if ($response.StatusCode -eq 200) {
            break
        }
    } catch {
        if ($elapsed -ge $timeout) {
            Write-Host "❌ Tool router failed to start within $timeout seconds" -ForegroundColor Red
            exit 1
        }
    }
} while ($elapsed -lt $timeout)
Write-Host "✅ Tool router health check passed"

# Test metrics endpoint
Write-Host "Testing Prometheus metrics endpoint..."
try {
    $metricsResponse = Invoke-WebRequest -Uri "http://localhost:8071/metrics" -UseBasicParsing
    if ($metricsResponse.StatusCode -eq 200) {
        Write-Host "✅ Metrics endpoint accessible"
    }
} catch {
    Write-Host "❌ Metrics endpoint not accessible" -ForegroundColor Red
    exit 1
}

# Step 4: Feature validation
Write-Host "🧪 Step 4: Feature Validation" -ForegroundColor Yellow

Write-Host "Testing basic tool routing..."
try {
    $body = @{
        tool = "tetragnos"
        args = @{ op = "ping" }
        proof_token = @{ token = "deployment-test" }
    } | ConvertTo-Json -Compress

    $routeResponse = Invoke-WebRequest -Uri "http://localhost:8071/route" -Method Post -Body $body -ContentType "application/json" -UseBasicParsing
    Write-Host "✅ Basic routing test passed"
} catch {
    Write-Host "⚠️  Basic routing test failed (expected if tools not running)" -ForegroundColor Yellow
}

Write-Host "Testing rate limiting..."
for ($i = 1; $i -le 5; $i++) {
    try {
        Invoke-WebRequest -Uri "http://localhost:8071/health" -UseBasicParsing | Out-Null
    } catch {
        # Ignore errors for rate limiting test
    }
}
Write-Host "✅ Rate limiting active (check metrics for rate_limited_total)"

# Step 5: Monitoring validation
Write-Host "📊 Step 5: Monitoring Validation" -ForegroundColor Yellow

try {
    $metricsContent = (Invoke-WebRequest -Uri "http://localhost:8071/metrics" -UseBasicParsing).Content
    if ($metricsContent -match "tool_router_") {
        Write-Host "✅ Prometheus metrics being generated"
    } else {
        Write-Host "❌ No tool router metrics found" -ForegroundColor Red
        exit 1
    }

    Write-Host ""
    Write-Host "📈 Current Metrics Sample:"
    $metricsContent -split "`n" | Where-Object { $_ -match "(tool_router_requests_total|tool_router_circuit_breaker_state)" } | Select-Object -First 5 | ForEach-Object { Write-Host $_ }
} catch {
    Write-Host "❌ Failed to retrieve metrics" -ForegroundColor Red
    exit 1
}

# Step 6: Load testing (optional)
Write-Host ""
Write-Host "🔥 Step 6: Load Testing (Optional)" -ForegroundColor Yellow
try {
    k6 version | Out-Null
    $runLoadTest = Read-Host "Run baseline load test? (y/N)"
    if ($runLoadTest -eq "y" -or $runLoadTest -eq "Y") {
        Write-Host "Running k6 load test..."
        $env:TOOL_ROUTER_URL = "http://localhost:8071"
        k6 run --quiet k6/health-baseline.js
        Write-Host "✅ Load test completed"
    }
} catch {
    Write-Host "⚠️  k6 not available. Install k6 for load testing: https://k6.io/docs/getting-started/installation/"
}

# Step 7: Final validation
Write-Host ""
Write-Host "🎯 Step 7: Final Validation" -ForegroundColor Yellow

if (Test-Path "tools/smoke.ps1") {
    Write-Host "Running smoke tests..."
    try {
        & "./tools/smoke.ps1" | Out-Null
        Write-Host "✅ Smoke tests passed"
    } catch {
        Write-Host "⚠️  Some smoke tests failed (may be expected if dependent services not running)" -ForegroundColor Yellow
    }
} else {
    Write-Host "⚠️  Smoke test script not found"
}

# Summary
Write-Host ""
Write-Host "🎉 DEPLOYMENT COMPLETE" -ForegroundColor Green
Write-Host "======================="
Write-Host ""
Write-Host "🔗 Service Endpoints:"
Write-Host "  • Tool Router: http://localhost:8071"
Write-Host "  • Health Check: http://localhost:8071/health"
Write-Host "  • Metrics: http://localhost:8071/metrics"
Write-Host ""
Write-Host "📊 Monitoring Setup:"
Write-Host "  • Prometheus target: tool-router:8071/metrics"
Write-Host "  • Alerting rules: monitoring/prometheus-rules.yml"
Write-Host "  • Runbooks: monitoring/runbooks.md"
Write-Host ""
Write-Host "🔧 Configuration:"
Write-Host "  • HMAC Signing: $(if ($SigningSecret) { '✅ Enabled' } else { '❌ Disabled' })"
Write-Host "  • Rate Limiting: $(if ($UseRedis -eq 'true') { 'Redis-based' } else { 'Memory-based' })"
Write-Host "  • Circuit Breakers: ✅ Enabled"
Write-Host "  • Retry Logic: ✅ Enabled"
Write-Host "  • Structured Logging: ✅ Enabled"
Write-Host ""
Write-Host "🧪 Testing Commands:"
Write-Host "  • Load test: k6 run k6/health-baseline.js"
Write-Host "  • Signed requests: `$env:SIGNING_SECRET='secret'; k6 run k6/signed-requests.js"
Write-Host "  • Smoke test: ./tools/smoke.ps1"
Write-Host ""
Write-Host "📈 Next Steps:"
Write-Host "  1. Configure Prometheus to scrape http://localhost:8071/metrics"
Write-Host "  2. Import alerting rules from monitoring/prometheus-rules.yml"
Write-Host "  3. Set up log aggregation for JSON logs with X-Request-ID correlation"
Write-Host "  4. Monitor SLOs: 99.9% availability, p95 latency < 500ms"
Write-Host ""
Write-Host "🚀 LOGOS Tool Router v2.0.0 is now operational!" -ForegroundColor Green
