# LOGOS PXL Core - Simple Service Starter
# Starts all services in background without terminal blocking

Write-Host "🚀 LOGOS PXL Core - Background Service Startup" -ForegroundColor Magenta
Write-Host "================================================" -ForegroundColor Magenta

# Service Configuration
$services = @(
    @{name="CRAWL"; port=8064; path="services.toolkits.crawl.app:app"; dir=""; env=@{}},
    @{name="TETRAGNOS"; port=8065; path="app:app"; dir="services\toolkits\tetragnos"; env=@{}},
    @{name="TELOS"; port=8066; path="app:app"; dir="services\toolkits\telos"; env=@{}},
    @{name="THONOC"; port=8067; path="app:app"; dir="services\toolkits\thonoc"; env=@{}},
    @{name="TOOL_ROUTER"; port=8071; path="services.tool_router.app:app"; dir=""; env=@{
        "TELOS_URL"="http://127.0.0.1:8066";
        "THONOC_URL"="http://127.0.0.1:8067";
        "TETRAGNOS_URL"="http://127.0.0.1:8065";
        "CRAWL_URL"="http://127.0.0.1:8064"
    }},
    @{name="EXECUTOR"; port=8072; path="services.executor.app:app"; dir=""; env=@{
        "TOOL_ROUTER_URL"="http://127.0.0.1:8071"
    }},
    @{name="INTERACTIVE_CHAT"; port=8080; path="main:chat_app"; dir="services\interactive_chat"; env=@{
        "LOGOS_API_URL"="http://127.0.0.1:8090";
        "TOOL_ROUTER_URL"="http://127.0.0.1:8071";
        "EXECUTOR_URL"="http://127.0.0.1:8072"
    }},
    @{name="LOGOS_API"; port=8090; path="logos_core.server:app"; dir=""; env=@{}}
)

# Start each service
$processes = @()
$rootDir = "C:\Users\proje\OneDrive\Desktop\Project_Directory\LOGOS_PXL_Core"

foreach ($svc in $services) {
    Write-Host "`n🔧 Starting $($svc.name) on port $($svc.port)..." -ForegroundColor Cyan
    
    # Set environment variables
    foreach ($envVar in $svc.env.GetEnumerator()) {
        [Environment]::SetEnvironmentVariable($envVar.Key, $envVar.Value, "Process")
        Write-Host "   Set $($envVar.Key)=$($envVar.Value)" -ForegroundColor Yellow
    }
    
    # Determine working directory
    $workDir = if ($svc.dir) { Join-Path $rootDir $svc.dir } else { $rootDir }
    
    # Start process in background
    $processArgs = @(
        "-m", "uvicorn", $svc.path,
        "--host", "127.0.0.1", 
        "--port", $svc.port,
        "--log-level", "warning"
    )
    
    try {
        $process = Start-Process -FilePath "python" -ArgumentList $processArgs -WorkingDirectory $workDir -WindowStyle Hidden -PassThru
        $processes += @{name=$svc.name; pid=$process.Id; port=$svc.port}
        Write-Host "   ✅ Started successfully (PID: $($process.Id))" -ForegroundColor Green
    } catch {
        Write-Host "   ❌ Failed to start: $($_.Exception.Message)" -ForegroundColor Red
    }
    
    # Small delay to prevent resource conflicts
    Start-Sleep 2
}

# Wait for services to initialize
Write-Host "`n⏳ Waiting for services to initialize..." -ForegroundColor Yellow
Start-Sleep 8

# Test service health
Write-Host "`n🔍 Testing service health..." -ForegroundColor Cyan
$allHealthy = $true

foreach ($proc in $processes) {
    try {
        $response = Invoke-WebRequest "http://127.0.0.1:$($proc.port)/health" -TimeoutSec 5 -UseBasicParsing
        Write-Host "   ✅ $($proc.name) (PID: $($proc.pid)): HEALTHY ($($response.StatusCode))" -ForegroundColor Green
    } catch {
        Write-Host "   ❌ $($proc.name) (PID: $($proc.pid)): NOT RESPONDING" -ForegroundColor Red
        $allHealthy = $false
    }
}

# Save process information
$processInfo = @{
    timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    processes = $processes
}
$processInfo | ConvertTo-Json -Depth 3 | Set-Content ".\.service_processes.json" -Encoding UTF8

if ($allHealthy) {
    Write-Host "`n🎉 ALL SERVICES STARTED SUCCESSFULLY!" -ForegroundColor Green
    Write-Host "Services are now running in the background." -ForegroundColor Green
    Write-Host "Terminals are free for other commands." -ForegroundColor Green
    Write-Host "`nTo check status later, run: Get-Content .\.service_processes.json | ConvertFrom-Json" -ForegroundColor Cyan
} else {
    Write-Host "`n⚠️ Some services failed to start properly." -ForegroundColor Yellow
}

Write-Host "`n📝 Process information saved to .service_processes.json" -ForegroundColor White