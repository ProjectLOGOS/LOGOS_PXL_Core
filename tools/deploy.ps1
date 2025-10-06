# LOGOS PXL Core Deployment Script
Write-Host "🚀 LOGOS PXL Core Deployment" -ForegroundColor Magenta
Write-Host "============================" -ForegroundColor Magenta

Write-Host "`n📦 Building services..." -ForegroundColor Cyan
docker-compose build logos-api tool-router executor interactive-chat tetragnos thonoc archon

if ($LASTEXITCODE -eq 0) {
    Write-Host "✅ Build successful" -ForegroundColor Green
    
    Write-Host "`n🔧 Starting services..." -ForegroundColor Cyan
    docker-compose up -d
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✅ Services started" -ForegroundColor Green
        
        Write-Host "`n⏳ Waiting for services to initialize..." -ForegroundColor Yellow
        Start-Sleep -Seconds 30
        
        Write-Host "`n🧪 Running smoke tests..." -ForegroundColor Cyan
        & ".\tools\smoke.ps1"
        
    } else {
        Write-Host "❌ Failed to start services" -ForegroundColor Red
        exit 1
    }
} else {
    Write-Host "❌ Build failed" -ForegroundColor Red
    exit 1
}