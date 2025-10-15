# LOGOS API Smoke Test - PowerShell Version
param(
    [string]$BaseUrl = $env:LOGOS_API_URL
)

if (-not $BaseUrl) {
    $BaseUrl = "http://localhost:8090"
}

Write-Host "🧪 LOGOS API Smoke Test" -ForegroundColor Blue
Write-Host "======================="

try {
    Write-Host "1. Testing health endpoint..."
    $healthResponse = Invoke-WebRequest -Uri "$BaseUrl/health" -UseBasicParsing
    if ($healthResponse.StatusCode -eq 200) {
        Write-Host "✅ Health check passed" -ForegroundColor Green
    }

    Write-Host ""
    Write-Host "2. Testing authorize_action endpoint..."
    $authBody = @{
        action = "cluster_texts"
        state = @{}
    } | ConvertTo-Json -Compress

    $authResponse = Invoke-WebRequest -Uri "$BaseUrl/authorize_action" -Method Post -Body $authBody -ContentType "application/json" -UseBasicParsing
    $authData = $authResponse.Content | ConvertFrom-Json
    
    try {
        Write-Host ($authResponse.Content | jq .)
    } catch {
        Write-Host $authResponse.Content
    }
    Write-Host "✅ Authorization successful" -ForegroundColor Green

    Write-Host ""
    Write-Host "3. Testing verify_kernel endpoint..."
    $kernelBody = @{
        kernel_hash = "deadbeef"
    } | ConvertTo-Json -Compress

    $kernelResponse = Invoke-WebRequest -Uri "$BaseUrl/verify_kernel" -Method Post -Body $kernelBody -ContentType "application/json" -UseBasicParsing
    try {
        Write-Host ($kernelResponse.Content | jq .)
    } catch {
        Write-Host $kernelResponse.Content
    }
    Write-Host "✅ Kernel verification working" -ForegroundColor Green

    Write-Host ""
    Write-Host "4. Testing proof token structure..."
    $proofToken = $authData.proof_token
    if ($proofToken.token -and $proofToken.exp -and $proofToken.action_sha256 -and $proofToken.nonce) {
        Write-Host "✅ Proof token has all required fields" -ForegroundColor Green
    } else {
        Write-Host "❌ Proof token missing required fields" -ForegroundColor Red
        exit 1
    }

    Write-Host ""
    Write-Host "🎉 All LOGOS API smoke tests passed!" -ForegroundColor Green
    Write-Host "API is ready for integration with tool router and chat services."

} catch {
    Write-Host "❌ Smoke test failed: $_" -ForegroundColor Red
    exit 1
}