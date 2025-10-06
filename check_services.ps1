# Quick service status check
Write-Host "🔍 LOGOS PXL Core Service Status" -ForegroundColor Cyan
Write-Host "=================================" -ForegroundColor Cyan

$services = @(
    @{name="CRAWL"; port=8064},
    @{name="TETRAGNOS"; port=8065}, 
    @{name="TELOS"; port=8066},
    @{name="THONOC"; port=8067},
    @{name="TOOL_ROUTER"; port=8071},
    @{name="EXECUTOR"; port=8072}
)

foreach ($svc in $services) {
    try {
        $response = Invoke-WebRequest "http://127.0.0.1:$($svc.port)/health" -TimeoutSec 3 -UseBasicParsing
        Write-Host "✅ $($svc.name): HEALTHY" -ForegroundColor Green
    } catch {
        Write-Host "❌ $($svc.name): DOWN" -ForegroundColor Red
    }
}

Write-Host "`n📊 Python Processes:" -ForegroundColor Yellow
Get-Process *python* -ErrorAction SilentlyContinue | Select-Object Id, @{Name="Memory(MB)";Expression={[math]::Round($_.WorkingSet/1MB,2)}} | Format-Table -AutoSize