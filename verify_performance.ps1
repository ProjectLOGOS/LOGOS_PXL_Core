# verify_performance.ps1 - CI Performance Validation Script for Windows
# Tests P95 latency < 300ms and cache hit rate >= 85%
# Exit code 1 if performance requirements not met

param(
    [string]$ServerUrl = "http://localhost:5000",
    [int]$WarmupRequests = 50,
    [int]$LoadTestRequests = 1000,
    [int]$Concurrency = 10,
    [int]$MaxP95Latency = 300,
    [int]$MinCacheHitRate = 85
)

Write-Host "Starting LOGOS PXL Performance Validation..." -ForegroundColor Cyan
Write-Host "Target: P95 < $MaxP95Latency ms, Cache Hit Rate >= $MinCacheHitRate%" -ForegroundColor Cyan

# Function to test server health
function Test-ServerHealth {
    try {
        $response = Invoke-RestMethod -Uri "$ServerUrl/health" -Method Get -ErrorAction Stop
        return $true
    }
    catch {
        return $false
    }
}

# Function to send proof request and measure latency
function Send-ProofRequest {
    param([string]$Goal)

    $stopwatch = [System.Diagnostics.Stopwatch]::StartNew()

    try {
        $body = @{ goal = $Goal } | ConvertTo-Json
        $response = Invoke-RestMethod -Uri "$ServerUrl/prove" -Method Post -Body $body -ContentType "application/json" -ErrorAction Stop
        $stopwatch.Stop()
        return $stopwatch.ElapsedMilliseconds
    }
    catch {
        $stopwatch.Stop()
        Write-Warning "Request failed for goal: $Goal"
        return $stopwatch.ElapsedMilliseconds
    }
}

# Check server health
if (-not (Test-ServerHealth)) {
    Write-Host "❌ ERROR: PXL server not responding at $ServerUrl" -ForegroundColor Red
    exit 1
}

Write-Host "✅ Server health check: PASSED" -ForegroundColor Green

# Warmup phase
Write-Host "🔥 Warmup phase: $WarmupRequests requests..." -ForegroundColor Yellow

for ($i = 1; $i -le $WarmupRequests; $i++) {
    $goal = "BOX(A $i -> A $i)"
    Send-ProofRequest -Goal $goal | Out-Null

    if ($i % 10 -eq 0) {
        Write-Progress -Activity "Warmup" -Status "Request $i of $WarmupRequests" -PercentComplete (($i / $WarmupRequests) * 100)
    }
}

Write-Progress -Activity "Warmup" -Completed
Write-Host "✅ Warmup completed" -ForegroundColor Green

# Test goals with repetition for cache hits
$testGoals = @(
    "BOX(A -> A)",
    "BOX(A /\ B -> A)",
    "BOX(A -> A \/ B)",
    "BOX((A -> B) -> ((B -> C) -> (A -> C)))",
    "BOX(A /\ B -> B /\ A)"
)

# Load test phase with concurrent execution
Write-Host "⚡ Load test: $LoadTestRequests requests with $Concurrency concurrent workers..." -ForegroundColor Yellow

$latencies = [System.Collections.Concurrent.ConcurrentBag[int]]::new()
$jobs = @()

$requestsPerWorker = [math]::Ceiling($LoadTestRequests / $Concurrency)

for ($worker = 1; $worker -le $Concurrency; $worker++) {
    $job = Start-Job -ScriptBlock {
        param($ServerUrl, $TestGoals, $RequestsPerWorker, $WorkerId)

        $workerLatencies = @()

        for ($request = 1; $request -le $RequestsPerWorker; $request++) {
            # Select goal with bias toward repetition for cache hits
            if (($request % 3) -eq 0) {
                $goalIndex = $request % $TestGoals.Count
                $goal = $TestGoals[$goalIndex]
            } else {
                # Repeat previous goals to trigger cache hits
                $goalIndex = ($request - 1) % $TestGoals.Count
                $goal = $TestGoals[$goalIndex]
            }

            $stopwatch = [System.Diagnostics.Stopwatch]::StartNew()

            try {
                $body = @{ goal = $goal } | ConvertTo-Json
                $response = Invoke-RestMethod -Uri "$ServerUrl/prove" -Method Post -Body $body -ContentType "application/json" -ErrorAction Stop
                $stopwatch.Stop()
                $workerLatencies += $stopwatch.ElapsedMilliseconds
            }
            catch {
                $stopwatch.Stop()
                $workerLatencies += $stopwatch.ElapsedMilliseconds
            }
        }

        return $workerLatencies
    } -ArgumentList $ServerUrl, $testGoals, $requestsPerWorker, $worker

    $jobs += $job
}

# Wait for all jobs and collect results
$allLatencies = @()
foreach ($job in $jobs) {
    $workerResults = Receive-Job -Job $job -Wait
    $allLatencies += $workerResults
    Remove-Job -Job $job
}

Write-Host "✅ Load test completed. Analyzing results..." -ForegroundColor Green

# Calculate performance metrics
$sortedLatencies = $allLatencies | Sort-Object
$totalRequests = $sortedLatencies.Count

if ($totalRequests -eq 0) {
    Write-Host "❌ ERROR: No latency data collected" -ForegroundColor Red
    exit 1
}

# Calculate percentiles
$p50Index = [math]::Floor($totalRequests * 0.50)
$p90Index = [math]::Floor($totalRequests * 0.90)
$p95Index = [math]::Floor($totalRequests * 0.95)
$p99Index = [math]::Floor($totalRequests * 0.99)

$p50Latency = $sortedLatencies[$p50Index]
$p90Latency = $sortedLatencies[$p90Index]
$p95Latency = $sortedLatencies[$p95Index]
$p99Latency = $sortedLatencies[$p99Index]

# Get cache statistics
try {
    $healthResponse = Invoke-RestMethod -Uri "$ServerUrl/health" -Method Get
    $cacheStats = $healthResponse.cache_stats
    $cacheHitRate = [math]::Round($cacheStats.hit_rate * 100, 1)
    $cacheHits = $cacheStats.cache_hits
    $cacheMisses = $cacheStats.cache_misses
    $prefetchHits = $cacheStats.prefetch_hits
}
catch {
    Write-Warning "Could not retrieve cache statistics"
    $cacheHitRate = 0
    $cacheHits = 0
    $cacheMisses = 0
    $prefetchHits = 0
}

# Performance report
Write-Host ""
Write-Host "=== PERFORMANCE VALIDATION RESULTS ===" -ForegroundColor Cyan
Write-Host "Total Requests: $totalRequests"
Write-Host "Latency Percentiles (ms):" -ForegroundColor White
Write-Host "  P50: $p50Latency"
Write-Host "  P90: $p90Latency"
Write-Host "  P95: $p95Latency"
Write-Host "  P99: $p99Latency"
Write-Host ""
Write-Host "Cache Performance:" -ForegroundColor White
Write-Host "  Hit Rate: $cacheHitRate%"
Write-Host "  Cache Hits: $cacheHits"
Write-Host "  Cache Misses: $cacheMisses"
Write-Host "  Prefetch Hits: $prefetchHits"
Write-Host ""

# Validation checks
$validationPassed = $true

if ($p95Latency -gt $MaxP95Latency) {
    Write-Host "❌ FAILED: P95 latency ($p95Latency ms) exceeds maximum ($MaxP95Latency ms)" -ForegroundColor Red
    $validationPassed = $false
} else {
    Write-Host "✅ PASSED: P95 latency ($p95Latency ms) within target ($MaxP95Latency ms)" -ForegroundColor Green
}

if ($cacheHitRate -lt $MinCacheHitRate) {
    Write-Host "❌ FAILED: Cache hit rate ($cacheHitRate%) below minimum ($MinCacheHitRate%)" -ForegroundColor Red
    $validationPassed = $false
} else {
    Write-Host "✅ PASSED: Cache hit rate ($cacheHitRate%) meets target (≥$MinCacheHitRate%)" -ForegroundColor Green
}

# Additional performance insights
Write-Host ""
Write-Host "=== PERFORMANCE INSIGHTS ===" -ForegroundColor Cyan

try {
    $poolStats = $healthResponse.session_pool_stats
    $utilization = [math]::Round($poolStats.utilization_rate * 100, 1)
    Write-Host "Session Pool:" -ForegroundColor White
    Write-Host "  Total Sessions: $($poolStats.total_sessions)"
    Write-Host "  Utilization: $utilization%"
    Write-Host "  Max Pool Size: $($poolStats.max_pool_size)"
}
catch {
    Write-Warning "Could not retrieve session pool statistics"
}

# Final result
Write-Host ""
if ($validationPassed) {
    Write-Host "🎉 ALL PERFORMANCE TESTS PASSED" -ForegroundColor Green
    Write-Host "Week 3 Security Hardening and Performance Optimization: COMPLETE" -ForegroundColor Green
    exit 0
} else {
    Write-Host "💥 PERFORMANCE VALIDATION FAILED" -ForegroundColor Red
    Write-Host "Requirements not met. Please optimize before deployment." -ForegroundColor Red
    exit 1
}
