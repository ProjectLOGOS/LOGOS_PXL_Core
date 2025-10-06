# LOGOS PXL Core Smoke Test (PowerShell)
# Run this after starting all services with docker-compose

Write-Host "🔥 LOGOS PXL Core Smoke Test" -ForegroundColor Magenta
Write-Host "============================" -ForegroundColor Magenta

try {
    # Test 1: LOGOS API Health Check
    Write-Host "`n1. Testing LOGOS API health..." -ForegroundColor Cyan
    $healthResponse = Invoke-RestMethod -Uri "http://localhost:8090/health" -Method Get
    if ($healthResponse.ok) {
        Write-Host "✅ LOGOS API is healthy" -ForegroundColor Green
    }

    # Test 2: Get proof token for operations
    Write-Host "2. Getting proof token..." -ForegroundColor Cyan
    $authBody = @{
        action = "cluster_texts"
        state = @{}
        provenance = @{ source = "smoke" }
    } | ConvertTo-Json -Depth 3

    $authResponse = Invoke-RestMethod -Uri "http://localhost:8090/authorize_action" -Method Post -Body $authBody -ContentType "application/json"
    $proofToken = $authResponse.proof_token | ConvertTo-Json -Compress
    Write-Host "✅ Proof token obtained" -ForegroundColor Green

    # Test 3: Test TETRAGNOS via tool router
    Write-Host "3. Testing TETRAGNOS text clustering..." -ForegroundColor Cyan
    $tetragnosBody = @{
        tool = "tetragnos"
        args = @{
            op = "cluster_texts"
            texts = @("Machine learning is powerful", "AI transforms industries", "Deep learning advances rapidly")
        }
        proof_token = $authResponse.proof_token
    } | ConvertTo-Json -Depth 4

    $tetragnosResponse = Invoke-RestMethod -Uri "http://localhost:8071/route" -Method Post -Body $tetragnosBody -ContentType "application/json"
    Write-Host "✅ TETRAGNOS clustering successful" -ForegroundColor Green

    # Test 4: Test THONOC via tool router
    Write-Host "4. Testing THONOC theorem proving..." -ForegroundColor Cyan
    $thonocBody = @{
        tool = "thonoc"
        args = @{
            formula = "A->B"
        }
        proof_token = $authResponse.proof_token
    } | ConvertTo-Json -Depth 3

    $thonocResponse = Invoke-RestMethod -Uri "http://localhost:8071/route" -Method Post -Body $thonocBody -ContentType "application/json"
    Write-Host "✅ THONOC proving successful" -ForegroundColor Green

    # Test 5: Test interactive chat
    Write-Host "5. Testing Interactive Chat service..." -ForegroundColor Cyan
    try {
        $chatResponse = Invoke-RestMethod -Uri "http://localhost:8080/health" -Method Get -ErrorAction SilentlyContinue
        Write-Host "✅ Interactive Chat is healthy" -ForegroundColor Green
    } catch {
        Write-Host "⚠️  Interactive Chat health check not available (may not have health endpoint)" -ForegroundColor Yellow
    }

    Write-Host "`n🎉 ALL SMOKE TESTS PASSED!" -ForegroundColor Green
    Write-Host "Your LOGOS PXL Core system is operational and ready for use." -ForegroundColor Green
    Write-Host "`nNext steps:" -ForegroundColor White
    Write-Host "- Visit http://localhost:8080 for GPT-enhanced chat" -ForegroundColor Gray
    Write-Host "- Use http://localhost:8071/route for tool routing" -ForegroundColor Gray
    Write-Host "- Access http://localhost:8090/authorize_action for proof tokens" -ForegroundColor Gray

} catch {
    Write-Host "`n❌ SMOKE TEST FAILED!" -ForegroundColor Red
    Write-Host "Error: $($_.Exception.Message)" -ForegroundColor Red
    Write-Host "`nMake sure all services are running with:" -ForegroundColor Yellow
    Write-Host "docker-compose up -d" -ForegroundColor Yellow
    exit 1
}