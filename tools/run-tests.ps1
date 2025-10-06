# LOGOS PXL Core Test Runner (PowerShell)
Write-Host "🧪 LOGOS PXL Core Test Suite" -ForegroundColor Magenta
Write-Host "============================" -ForegroundColor Magenta

Write-Host "`n📦 Installing test dependencies..." -ForegroundColor Cyan
python -m pip install --upgrade pip
pip install -e .[dev]

if ($LASTEXITCODE -eq 0) {
    Write-Host "✅ Dependencies installed" -ForegroundColor Green
    
    Write-Host "`n🔍 Running linting..." -ForegroundColor Cyan
    ruff check .
    
    if ($LASTEXITCODE -eq 0) {
        Write-Host "✅ Linting passed" -ForegroundColor Green
        
        Write-Host "`n📐 Running type checking..." -ForegroundColor Cyan
        mypy .
        
        if ($LASTEXITCODE -eq 0) {
            Write-Host "✅ Type checking passed" -ForegroundColor Green
            
            Write-Host "`n🧪 Running tests..." -ForegroundColor Cyan
            pytest -q
            
            if ($LASTEXITCODE -eq 0) {
                Write-Host "`n🎉 ALL TESTS PASSED!" -ForegroundColor Green
            } else {
                Write-Host "`n❌ Tests failed" -ForegroundColor Red
                exit 1
            }
        } else {
            Write-Host "❌ Type checking failed" -ForegroundColor Red
            exit 1
        }
    } else {
        Write-Host "❌ Linting failed" -ForegroundColor Red
        exit 1
    }
} else {
    Write-Host "❌ Failed to install dependencies" -ForegroundColor Red
    exit 1
}