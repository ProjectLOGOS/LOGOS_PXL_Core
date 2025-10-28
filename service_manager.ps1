#!/usr/bin/env pwsh
# LOGOS PXL Core Service Manager
# Manages all microservices with proper background process handling

param(
    [Parameter(Mandatory=$true)]
    [ValidateSet("start", "stop", "restart", "status", "test")]
    [string]$Action,
    
    [string]$Service = "all",
    [switch]$Verbose
)

$ErrorActionPreference = "Stop"

# Service Definitions
$Services = @{
    "crawl" = @{
        Name = "CRAWL"
        Port = 8064
        Path = "services.toolkits.crawl.app:app"
        WorkingDir = "C:\Users\proje\OneDrive\Desktop\Project_Directory\LOGOS_PXL_Core"
        EnvVars = @{}
    }
    "tetragnos" = @{
        Name = "TETRAGNOS" 
        Port = 8065
        Path = "app:app"
        WorkingDir = "C:\Users\proje\OneDrive\Desktop\Project_Directory\LOGOS_PXL_Core\services\toolkits\tetragnos"
        EnvVars = @{}
    }
    "telos" = @{
        Name = "TELOS"
        Port = 8066
        Path = "app:app" 
        WorkingDir = "C:\Users\proje\OneDrive\Desktop\Project_Directory\LOGOS_PXL_Core\services\toolkits\telos"
        EnvVars = @{}
    }
    "thonoc" = @{
        Name = "THONOC"
        Port = 8067
        Path = "app:app"
        WorkingDir = "C:\Users\proje\OneDrive\Desktop\Project_Directory\LOGOS_PXL_Core\services\toolkits\thonoc" 
        EnvVars = @{}
    }
    "tool_router" = @{
        Name = "TOOL_ROUTER"
        Port = 8071
        Path = "services.tool_router.app:app"
        WorkingDir = "C:\Users\proje\OneDrive\Desktop\Project_Directory\LOGOS_PXL_Core"
        EnvVars = @{
            "TELOS_URL" = "http://127.0.0.1:8066"
            "THONOC_URL" = "http://127.0.0.1:8067" 
            "TETRAGNOS_URL" = "http://127.0.0.1:8065"
            "WEB_URL" = "http://127.0.0.1:8061"
            "DB_URL" = "http://127.0.0.1:8062"
            "FS_URL" = "http://127.0.0.1:8063"
            "CRAWL_URL" = "http://127.0.0.1:8064"
        }
    }
    "executor" = @{
        Name = "EXECUTOR"
        Port = 8072
        Path = "services.executor.app:app"
        WorkingDir = "C:\Users\proje\OneDrive\Desktop\Project_Directory\LOGOS_PXL_Core"
        EnvVars = @{
            "TOOL_ROUTER_URL" = "http://127.0.0.1:8071"
        }
    }
    "logos_api" = @{
        Name = "LOGOS_API"
        Port = 8090
        Path = "logos_core.server:app"
        WorkingDir = "C:\Users\proje\OneDrive\Desktop\Project_Directory\LOGOS_PXL_Core"
        EnvVars = @{}
    }
}

# Process tracking file
$ProcessFile = "C:\Users\proje\OneDrive\Desktop\Project_Directory\LOGOS_PXL_Core\.service_processes.json"

function Write-ServiceLog {
    param([string]$Message, [string]$Level = "INFO")
    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $color = switch($Level) {
        "INFO" { "White" }
        "SUCCESS" { "Green" }
        "WARNING" { "Yellow" }
        "ERROR" { "Red" }
        default { "White" }
    }
    Write-Host "[$timestamp] $Message" -ForegroundColor $color
}

function Get-ServiceProcesses {
    if (Test-Path $ProcessFile) {
        return Get-Content $ProcessFile | ConvertFrom-Json -AsHashtable
    }
    return @{}
}

function Save-ServiceProcesses {
    param([hashtable]$Processes)
    $Processes | ConvertTo-Json -Depth 3 | Set-Content $ProcessFile -Encoding UTF8
}

function Start-ServiceProcess {
    param(
        [string]$ServiceKey,
        [hashtable]$ServiceConfig
    )
    
    Write-ServiceLog "Starting $($ServiceConfig.Name) on port $($ServiceConfig.Port)..." "INFO"
    
    # Set environment variables
    foreach ($envVar in $ServiceConfig.EnvVars.GetEnumerator()) {
        Set-Item -Path "env:$($envVar.Key)" -Value $envVar.Value
        if ($Verbose) {
            Write-ServiceLog "  Set $($envVar.Key)=$($envVar.Value)" "INFO"
        }
    }
    
    # Start process in background
    $processArgs = @(
        "-m", "uvicorn", $ServiceConfig.Path,
        "--host", "127.0.0.1",
        "--port", $ServiceConfig.Port,
        "--log-level", "warning"
    )
    
    $process = Start-Process -FilePath "python" -ArgumentList $processArgs -WorkingDirectory $ServiceConfig.WorkingDir -WindowStyle Hidden -PassThru
    
    if ($process) {
        Write-ServiceLog "✅ $($ServiceConfig.Name) started (PID: $($process.Id))" "SUCCESS"
        
        # Save process info
        $processes = Get-ServiceProcesses
        $processes[$ServiceKey] = @{
            PID = $process.Id
            Port = $ServiceConfig.Port
            StartTime = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
            Name = $ServiceConfig.Name
        }
        Save-ServiceProcesses $processes
        
        return $process.Id
    } else {
        Write-ServiceLog "❌ Failed to start $($ServiceConfig.Name)" "ERROR"
        return $null
    }
}

function Stop-ServiceProcess {
    param([string]$ServiceKey)
    
    $processes = Get-ServiceProcesses
    if ($processes.ContainsKey($ServiceKey)) {
        $processInfo = $processes[$ServiceKey]
        Write-ServiceLog "Stopping $($processInfo.Name) (PID: $($processInfo.PID))..." "INFO"
        
        try {
            Stop-Process -Id $processInfo.PID -Force -ErrorAction Stop
            Write-ServiceLog "✅ $($processInfo.Name) stopped" "SUCCESS"
        } catch {
            Write-ServiceLog "⚠️ Process $($processInfo.PID) may already be stopped" "WARNING"
        }
        
        # Remove from tracking
        $processes.Remove($ServiceKey)
        Save-ServiceProcesses $processes
    } else {
        Write-ServiceLog "⚠️ No tracked process found for $ServiceKey" "WARNING"
    }
}

function Test-ServiceHealth {
    param([hashtable]$ServiceConfig)
    
    try {
        $response = Invoke-WebRequest "http://127.0.0.1:$($ServiceConfig.Port)/health" -TimeoutSec 3 -UseBasicParsing
        return @{
            Status = "HEALTHY"
            StatusCode = $response.StatusCode
            ResponseTime = $response.Headers["X-Response-Time"]
        }
    } catch {
        return @{
            Status = "DOWN"
            Error = $_.Exception.Message
        }
    }
}

function Show-ServiceStatus {
    Write-ServiceLog "=== LOGOS PXL CORE SERVICE STATUS ===" "INFO"
    Write-Host ""
    
    $processes = Get-ServiceProcesses()
    $allHealthy = $true
    
    foreach ($serviceKey in $Services.Keys | Sort-Object) {
        $service = $Services[$serviceKey]
        $processInfo = $processes[$serviceKey]
        
        Write-Host "🔧 $($service.Name) (Port: $($service.Port))" -ForegroundColor Cyan
        
        if ($processInfo) {
            # Check if process is still running
            $isRunning = Get-Process -Id $processInfo.PID -ErrorAction SilentlyContinue
            if ($isRunning) {
                Write-Host "   Process: RUNNING (PID: $($processInfo.PID), Started: $($processInfo.StartTime))" -ForegroundColor Green
                
                # Test health endpoint
                $health = Test-ServiceHealth $service
                if ($health.Status -eq "HEALTHY") {
                    Write-Host "   Health: ✅ HEALTHY ($($health.StatusCode))" -ForegroundColor Green
                } else {
                    Write-Host "   Health: ❌ $($health.Status) - $($health.Error)" -ForegroundColor Red
                    $allHealthy = $false
                }
            } else {
                Write-Host "   Process: ❌ STOPPED (PID $($processInfo.PID) not found)" -ForegroundColor Red
                $allHealthy = $false
            }
        } else {
            Write-Host "   Process: ❌ NOT STARTED" -ForegroundColor Red
            $allHealthy = $false
        }
        Write-Host ""
    }
    
    if ($allHealthy) {
        Write-ServiceLog "🎉 ALL SERVICES HEALTHY AND OPERATIONAL" "SUCCESS"
    } else {
        Write-ServiceLog "⚠️ Some services need attention" "WARNING"
    }
    
    return $allHealthy
}

function Test-ServiceIntegration {
    Write-ServiceLog "=== INTEGRATION TESTS ===" "INFO"
    
    # Test TELOS via Tool Router
    try {
        $telosTest = @{
            tool = "telos"
            args = @{
                op = "forecast_series"
                series = @(1.0,2.0,3.0,4.0,5.0,6.0,7.0,8.0)
                horizon = 4
            }
            proof_token = @{
                id = "integration-test"
                kernel_hash = "verified"
            }
        } | ConvertTo-Json -Depth 3
        
        $result = Invoke-RestMethod -Uri "http://127.0.0.1:8071/route" -Method POST -Body $telosTest -ContentType "application/json" -TimeoutSec 10
        Write-ServiceLog "✅ TELOS Integration: SUCCESS (Forecast: $($result.result.forecast -join ', '))" "SUCCESS"
    } catch {
        Write-ServiceLog "❌ TELOS Integration: FAILED - $($_.Exception.Message)" "ERROR"
    }
    
    # Test TETRAGNOS via Tool Router
    try {
        $tetragnos_test = @{
            tool = "tetragnos"
            args = @{
                op = "cluster_texts"
                texts = @("Hello world", "Goodbye world", "Machine learning", "Deep learning")
                n_clusters = 2
            }
            proof_token = @{
                id = "integration-test"
                kernel_hash = "verified"
            }
        } | ConvertTo-Json -Depth 3
        
        $result = Invoke-RestMethod -Uri "http://127.0.0.1:8071/route" -Method POST -Body $tetragnos_test -ContentType "application/json" -TimeoutSec 10
        Write-ServiceLog "✅ TETRAGNOS Integration: SUCCESS (Clusters: $($result.result.n_clusters))" "SUCCESS"
    } catch {
        Write-ServiceLog "❌ TETRAGNOS Integration: FAILED - $($_.Exception.Message)" "ERROR"
    }
}

# Main execution logic
switch ($Action) {
    "start" {
        Write-ServiceLog "🚀 Starting LOGOS PXL Core Services..." "INFO"
        
        if ($Service -eq "all") {
            # Start in dependency order
            $startOrder = @("crawl", "tetragnos", "telos", "thonoc", "tool_router", "executor", "logos_api")
            foreach ($serviceKey in $startOrder) {
                Start-ServiceProcess $serviceKey $Services[$serviceKey]
                Start-Sleep 2  # Allow service to initialize
            }
        } else {
            if ($Services.ContainsKey($Service)) {
                Start-ServiceProcess $Service $Services[$Service]
            } else {
                Write-ServiceLog "❌ Unknown service: $Service" "ERROR"
                exit 1
            }
        }
        
        Write-ServiceLog "⏳ Waiting for services to initialize..." "INFO"
        Start-Sleep 5
        Show-ServiceStatus
    }
    
    "stop" {
        Write-ServiceLog "🛑 Stopping LOGOS PXL Core Services..." "INFO"
        
        if ($Service -eq "all") {
            # Stop all tracked processes
            foreach ($serviceKey in $Services.Keys) {
                Stop-ServiceProcess $serviceKey
            }
            
            # Also kill any stray python processes on our ports
            Get-Process *python* -ErrorAction SilentlyContinue | ForEach-Object {
                $cmdline = (Get-WmiObject Win32_Process -Filter "ProcessId = $($_.Id)" -ErrorAction SilentlyContinue).CommandLine
                if ($cmdline -and ($cmdline -match ":806[4-7]|:807[12]|:8090")) {
                    Stop-Process -Id $_.Id -Force -ErrorAction SilentlyContinue
                }
            }
        } else {
            Stop-ServiceProcess $Service
        }
    }
    
    "restart" {
        Write-ServiceLog "🔄 Restarting LOGOS PXL Core Services..." "INFO"
        & $PSCommandPath -Action "stop" -Service $Service
        Start-Sleep 3
        & $PSCommandPath -Action "start" -Service $Service
    }
    
    "status" {
        Show-ServiceStatus
    }
    
    "test" {
        $healthy = Show-ServiceStatus
        if ($healthy) {
            Test-ServiceIntegration
        } else {
            Write-ServiceLog "❌ Cannot run integration tests - some services are down" "ERROR"
        }
    }
}

Write-ServiceLog "Service management operation completed." "INFO"