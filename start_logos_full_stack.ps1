# PowerShell Script for LOGOS AGI Full Stack Deployment
# Enhanced version with comprehensive service management

param(
    [Parameter()]
    [ValidateSet("deploy", "status", "shutdown", "restart", "logs", "health")]
    [string]$Action = "deploy",

    [Parameter()]
    [ValidateSet("docker", "local", "auto")]
    [string]$Mode = "auto",

    [Parameter()]
    [string]$ConfigPath = "deployment_config.yaml",

    [Parameter()]
    [switch]$Monitor,

    [Parameter()]
    [switch]$Verbose,

    [Parameter()]
    [switch]$Force
)

# Set up logging
$LogLevel = if ($Verbose) { "DEBUG" } else { "INFO" }
$Timestamp = Get-Date -Format "yyyy-MM-dd_HH-mm-ss"
$LogFile = "logs\deployment_$Timestamp.log"

# Ensure logs directory exists
New-Item -ItemType Directory -Force -Path "logs" | Out-Null

function Write-LogMessage {
    param(
        [string]$Message,
        [ValidateSet("INFO", "WARN", "ERROR", "DEBUG", "SUCCESS")]
        [string]$Level = "INFO"
    )

    $timestamp = Get-Date -Format "yyyy-MM-dd HH:mm:ss"
    $emoji = switch ($Level) {
        "INFO" { "ℹ️" }
        "WARN" { "⚠️" }
        "ERROR" { "❌" }
        "DEBUG" { "🔍" }
        "SUCCESS" { "✅" }
    }

    $logEntry = "[$timestamp] [$Level] $Message"

    # Console output with colors
    switch ($Level) {
        "INFO" { Write-Host "$emoji $Message" -ForegroundColor Cyan }
        "WARN" { Write-Host "$emoji $Message" -ForegroundColor Yellow }
        "ERROR" { Write-Host "$emoji $Message" -ForegroundColor Red }
        "DEBUG" { if ($Verbose) { Write-Host "$emoji $Message" -ForegroundColor DarkGray } }
        "SUCCESS" { Write-Host "$emoji $Message" -ForegroundColor Green }
    }

    # File output
    Add-Content -Path $LogFile -Value $logEntry
}

function Test-Prerequisites {
    Write-LogMessage "Checking deployment prerequisites..." "INFO"

    $prerequisites = @()

    # Check Python
    try {
        $pythonVersion = python --version 2>&1
        if ($LASTEXITCODE -eq 0) {
            Write-LogMessage "Python: $pythonVersion" "SUCCESS"
        } else {
            $prerequisites += "Python 3.8+ is required"
        }
    } catch {
        $prerequisites += "Python 3.8+ is required"
    }

    # Check Docker (if needed)
    if ($Mode -eq "docker" -or $Mode -eq "auto") {
        try {
            $dockerVersion = docker --version 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-LogMessage "Docker: $dockerVersion" "SUCCESS"

                # Check Docker Compose
                $composeVersion = docker-compose --version 2>&1
                if ($LASTEXITCODE -eq 0) {
                    Write-LogMessage "Docker Compose: $composeVersion" "SUCCESS"
                } else {
                    $prerequisites += "Docker Compose is required for Docker deployment"
                }
            } else {
                if ($Mode -eq "docker") {
                    $prerequisites += "Docker is required for Docker deployment mode"
                } else {
                    Write-LogMessage "Docker not available, will use local mode" "WARN"
                }
            }
        } catch {
            if ($Mode -eq "docker") {
                $prerequisites += "Docker is required for Docker deployment mode"
            }
        }
    }

    # Check required Python packages
    $requiredPackages = @("uvicorn", "fastapi", "pydantic", "requests", "pyyaml", "psutil")
    foreach ($package in $requiredPackages) {
        try {
            $null = python -c "import $package" 2>&1
            if ($LASTEXITCODE -eq 0) {
                Write-LogMessage "Package $package: Available" "DEBUG"
            } else {
                $prerequisites += "Python package '$package' is required"
            }
        } catch {
            $prerequisites += "Python package '$package' is required"
        }
    }

    if ($prerequisites.Count -gt 0) {
        Write-LogMessage "Missing prerequisites:" "ERROR"
        foreach ($prereq in $prerequisites) {
            Write-LogMessage "  - $prereq" "ERROR"
        }

        Write-LogMessage "Installing missing Python packages..." "INFO"
        try {
            $packagesToInstall = $requiredPackages -join " "
            python -m pip install $packagesToInstall.Split(" ")
            if ($LASTEXITCODE -eq 0) {
                Write-LogMessage "Python packages installed successfully" "SUCCESS"
            } else {
                Write-LogMessage "Failed to install some Python packages" "ERROR"
                return $false
            }
        } catch {
            Write-LogMessage "Failed to install Python packages: $_" "ERROR"
            return $false
        }
    }

    return $true
}

function Start-LogosDeployment {
    Write-LogMessage "🚀 Starting LOGOS AGI Full Stack Deployment" "INFO"
    Write-LogMessage "=" * 60 "INFO"

    # Check prerequisites
    if (-not (Test-Prerequisites)) {
        Write-LogMessage "Prerequisites check failed" "ERROR"
        return $false
    }

    # Prepare deployment arguments
    $deployArgs = @("deploy_full_stack.py")

    if ($ConfigPath -and (Test-Path $ConfigPath)) {
        $deployArgs += "--config", $ConfigPath
    }

    $deployArgs += "--mode", $Mode.ToLower()

    if ($Monitor) {
        $deployArgs += "--monitor"
    }

    Write-LogMessage "Executing deployment with arguments: $($deployArgs -join ' ')" "DEBUG"

    try {
        # Start the deployment
        $process = Start-Process -FilePath "python" -ArgumentList $deployArgs -NoNewWindow -PassThru

        # Wait for initial startup
        Start-Sleep -Seconds 5

        if (-not $process.HasExited) {
            Write-LogMessage "Deployment process started successfully (PID: $($process.Id))" "SUCCESS"

            # Monitor deployment
            $timeout = 300  # 5 minutes
            $elapsed = 0
            $interval = 10

            while ($elapsed -lt $timeout -and -not $process.HasExited) {
                Start-Sleep -Seconds $interval
                $elapsed += $interval

                # Check if services are responding
                $healthCheck = Test-ServicesHealth
                if ($healthCheck.Overall) {
                    Write-LogMessage "Services are responding, deployment appears successful" "SUCCESS"
                    break
                }

                Write-LogMessage "Waiting for services to start... ($elapsed/$timeout seconds)" "INFO"
            }

            if ($process.HasExited) {
                $exitCode = $process.ExitCode
                if ($exitCode -eq 0) {
                    Write-LogMessage "Deployment completed successfully" "SUCCESS"
                } else {
                    Write-LogMessage "Deployment failed with exit code: $exitCode" "ERROR"
                    return $false
                }
            }

            return $true
        } else {
            Write-LogMessage "Deployment process exited immediately" "ERROR"
            return $false
        }
    } catch {
        Write-LogMessage "Failed to start deployment: $_" "ERROR"
        return $false
    }
}

function Get-DeploymentStatus {
    Write-LogMessage "📊 Getting deployment status..." "INFO"

    try {
        $statusOutput = python deploy_full_stack.py --status 2>&1
        if ($LASTEXITCODE -eq 0) {
            $status = $statusOutput | ConvertFrom-Json

            Write-LogMessage "Deployment Status:" "INFO"
            Write-LogMessage "  Active: $($status.deployment_active)" "INFO"
            Write-LogMessage "  Mode: $($status.mode.ToUpper())" "INFO"
            Write-LogMessage "  Started: $($status.started_at)" "INFO"
            Write-LogMessage "  Services: $($status.healthy_count)/$($status.services_count) healthy" "INFO"

            Write-LogMessage "`nService Health:" "INFO"
            foreach ($serviceName in $status.health.services.PSObject.Properties.Name) {
                $service = $status.health.services.$serviceName
                $statusIcon = switch ($service.status) {
                    "healthy" { "✅" }
                    "unhealthy" { "⚠️" }
                    "unreachable" { "❌" }
                }
                Write-LogMessage "  $statusIcon $serviceName ($($service.port)): $($service.status)" "INFO"
            }

            Write-LogMessage "`nKey Endpoints:" "INFO"
            $keyEndpoints = @{
                "LOGOS Core API" = "http://localhost:8090"
                "Interactive Chat" = "http://localhost:8080"
                "Probe Console" = "http://localhost:8081"
                "Archon Gateway" = "http://localhost:8075"
            }

            foreach ($endpoint in $keyEndpoints.GetEnumerator()) {
                Write-LogMessage "  $($endpoint.Key): $($endpoint.Value)" "INFO"
            }

            return $true
        } else {
            Write-LogMessage "Failed to get deployment status" "ERROR"
            return $false
        }
    } catch {
        Write-LogMessage "Error getting status: $_" "ERROR"
        return $false
    }
}

function Stop-LogosDeployment {
    Write-LogMessage "🛑 Shutting down LOGOS deployment..." "INFO"

    try {
        python deploy_full_stack.py --shutdown
        if ($LASTEXITCODE -eq 0) {
            Write-LogMessage "Deployment shutdown completed" "SUCCESS"
            return $true
        } else {
            Write-LogMessage "Shutdown command failed" "ERROR"
            return $false
        }
    } catch {
        Write-LogMessage "Error during shutdown: $_" "ERROR"
        return $false
    }
}

function Test-ServicesHealth {
    $services = @{
        "LOGOS Core" = "http://localhost:8090/health"
        "Interactive Chat" = "http://localhost:8080"
        "Probe Console" = "http://localhost:8081"
        "Archon" = "http://localhost:8075/health"
    }

    $healthResults = @{}
    $overallHealthy = $true

    foreach ($service in $services.GetEnumerator()) {
        try {
            $response = Invoke-WebRequest -Uri $service.Value -TimeoutSec 5 -UseBasicParsing
            $healthResults[$service.Key] = $response.StatusCode -eq 200
            if (-not $healthResults[$service.Key]) {
                $overallHealthy = $false
            }
        } catch {
            $healthResults[$service.Key] = $false
            $overallHealthy = $false
        }
    }

    return @{
        Services = $healthResults
        Overall = $overallHealthy
    }
}

function Restart-LogosDeployment {
    Write-LogMessage "🔄 Restarting LOGOS deployment..." "INFO"

    if (Stop-LogosDeployment) {
        Start-Sleep -Seconds 5
        return Start-LogosDeployment
    } else {
        Write-LogMessage "Failed to stop deployment for restart" "ERROR"
        return $false
    }
}

function Show-DeploymentLogs {
    param([int]$Lines = 100)

    Write-LogMessage "📜 Showing recent deployment logs..." "INFO"

    $logFiles = Get-ChildItem -Path "logs" -Filter "*.log" | Sort-Object LastWriteTime -Descending

    if ($logFiles.Count -gt 0) {
        $latestLog = $logFiles[0]
        Write-LogMessage "Latest log file: $($latestLog.Name)" "INFO"

        Get-Content -Path $latestLog.FullName -Tail $Lines
    } else {
        Write-LogMessage "No log files found" "WARN"
    }
}

# Main execution
Write-LogMessage "LOGOS AGI Full Stack Deployment Manager" "INFO"
Write-LogMessage "Action: $Action, Mode: $Mode" "INFO"

$success = $false

switch ($Action.ToLower()) {
    "deploy" {
        $success = Start-LogosDeployment
    }
    "status" {
        $success = Get-DeploymentStatus
    }
    "shutdown" {
        $success = Stop-LogosDeployment
    }
    "restart" {
        $success = Restart-LogosDeployment
    }
    "logs" {
        Show-DeploymentLogs
        $success = $true
    }
    "health" {
        $health = Test-ServicesHealth
        Write-LogMessage "Health Check Results:" "INFO"
        foreach ($service in $health.Services.GetEnumerator()) {
            $status = if ($service.Value) { "✅ Healthy" } else { "❌ Unhealthy" }
            Write-LogMessage "  $($service.Key): $status" "INFO"
        }
        Write-LogMessage "Overall: $(if ($health.Overall) { '✅ Healthy' } else { '❌ Unhealthy' })" "INFO"
        $success = $true
    }
    default {
        Write-LogMessage "Unknown action: $Action" "ERROR"
        Write-LogMessage "Valid actions: deploy, status, shutdown, restart, logs, health" "INFO"
        $success = $false
    }
}

if ($success) {
    Write-LogMessage "✅ Operation completed successfully" "SUCCESS"
    exit 0
} else {
    Write-LogMessage "❌ Operation failed" "ERROR"
    exit 1
}
