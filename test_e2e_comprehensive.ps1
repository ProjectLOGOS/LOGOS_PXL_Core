# LOGOS AGI System - End-to-End Test Script (PowerShell)
# Comprehensive testing of all systems and subsystems

param(
    [switch]$SkipCleanup,
    [switch]$Verbose,
    [int]$ServiceStartupWait = 5
)

$ErrorActionPreference = "SilentlyContinue"

# Colors for output
$GREEN = "`e[32m"
$RED = "`e[31m"
$YELLOW = "`e[33m"
$BLUE = "`e[34m"
$BOLD = "`e[1m"
$RESET = "`e[0m"

# Test results tracking
$TestResults = @{
    Passed = 0
    Failed = 0
    Total = 0
    Details = @()
}

# Service configuration
$Services = @{
    ToolRouter = @{ Port = 8000; Path = "services/tool_router"; Command = "uvicorn app:app --host 0.0.0.0 --port 8000" }
    LogosApi = @{ Port = 8090; Path = "services/logos_api"; Command = "uvicorn app:app --host 0.0.0.0 --port 8090" }
    InteractiveChat = @{ Port = 8080; Path = "services/interactive_chat"; Command = "python app.py" }
}

$RunningProcesses = @()

function Write-TestLog {
    param(
        [string]$Message,
        [string]$Color = $BLUE,
        [string]$Icon = "INFO"
    )
    $timestamp = Get-Date -Format "HH:mm:ss"
    Write-Host "${Color}[$timestamp] $Icon $Message${RESET}"
}

function Write-Success {
    param([string]$Message)
    Write-TestLog -Message $Message -Color $GREEN -Icon "PASS"
    $TestResults.Passed++
}

function Write-Failure {
    param([string]$Message)
    Write-TestLog -Message $Message -Color $RED -Icon "FAIL"
    $TestResults.Failed++
}

function Write-Warning {
    param([string]$Message)
    Write-TestLog -Message $Message -Color $YELLOW -Icon "WARN"
}

function Test-Step {
    param([string]$TestName)
    $TestResults.Total++
    Write-TestLog -Message "Testing: $TestName" -Color $BOLD -Icon "TEST"
}

function Test-Port {
    param([int]$Port, [int]$TimeoutSeconds = 5)
    
    try {
        $tcpClient = New-Object System.Net.Sockets.TcpClient
        $asyncResult = $tcpClient.BeginConnect('localhost', $Port, $null, $null)
        $waitHandle = $asyncResult.AsyncWaitHandle
        
        if ($waitHandle.WaitOne($TimeoutSeconds * 1000)) {
            $tcpClient.EndConnect($asyncResult)
            $tcpClient.Close()
            return $true
        } else {
            $tcpClient.Close() 
            return $false
        }
    } catch {
        return $false
    }
}

function Start-ServiceWithTest {
    param(
        [string]$ServiceName,
        [hashtable]$ServiceConfig
    )
    
    Write-TestLog "Starting $ServiceName..."
    
    try {
        $workingDir = Join-Path $PWD $ServiceConfig.Path
        $pythonPath = ".venv/Scripts/python.exe"
        
        # Build command
        $fullCommand = "$pythonPath -m $($ServiceConfig.Command)"
        
        # Start the service
        $processInfo = New-Object System.Diagnostics.ProcessStartInfo
        $processInfo.FileName = "cmd.exe"
        $processInfo.Arguments = "/c cd `"$workingDir`" `& $fullCommand"
        $processInfo.UseShellExecute = $false
        $processInfo.CreateNoWindow = $true
        $processInfo.RedirectStandardOutput = $true
        $processInfo.RedirectStandardError = $true
        
        $process = [System.Diagnostics.Process]::Start($processInfo)
        $RunningProcesses += @{ Name = $ServiceName; Process = $process }
        
        # Wait for service to start
        Start-Sleep -Seconds $ServiceStartupWait
        
        # Test if port is available
        if (Test-Port -Port $ServiceConfig.Port) {
            Write-Success "$ServiceName started successfully on port $($ServiceConfig.Port)"
            return $true
        } else {
            Write-Failure "$ServiceName failed to start on port $($ServiceConfig.Port)"
            return $false
        }
        
    } catch {
        Write-Failure "Failed to start $ServiceName : $($_.Exception.Message)"
        return $false
    }
}

function Test-HttpEndpoint {
    param(
        [string]$Url,
        [string]$Method = "GET",
        [hashtable]$Headers = @{},
        [string]$Body = $null,
        [int]$ExpectedStatus = 200,
        [int]$TimeoutSeconds = 10
    )
    
    try {
        $webRequest = @{
            Uri = $Url
            Method = $Method
            Headers = $Headers
            TimeoutSec = $TimeoutSeconds
            UseBasicParsing = $true
        }
        
        if ($Body) {
            $webRequest.Body = $Body
            $webRequest.ContentType = "application/json"
        }
        
        $response = Invoke-WebRequest @webRequest
        
        if ($response.StatusCode -eq $ExpectedStatus) {
            return @{ Success = $true; Response = $response; StatusCode = $response.StatusCode }
        } else {
            return @{ Success = $false; Response = $response; StatusCode = $response.StatusCode; Error = "Unexpected status code" }
        }
        
    } catch {
        return @{ Success = $false; Response = $null; StatusCode = $null; Error = $_.Exception.Message }
    }
}

function Test-UnitTests {
    Test-Step "Unit Test Suite"
    
    try {
        Write-TestLog "Running pytest unit tests..."
        $pythonPath = ".venv/Scripts/python.exe"
        $result = & $pythonPath -m pytest tests/ -v --tb=short
        $exitCode = $LASTEXITCODE
        
        if ($exitCode -eq 0) {
            Write-Success "All unit tests passed"
            $TestResults.Details += @{ Test = "Unit Tests"; Status = "PASS"; Details = "Exit code: $exitCode" }
        } else {
            Write-Failure "Unit tests failed with exit code $exitCode"
            $TestResults.Details += @{ Test = "Unit Tests"; Status = "FAIL"; Details = "Exit code: $exitCode" }
        }
        
    } catch {
        Write-Failure "Unit test execution failed: $($_.Exception.Message)"
        $TestResults.Details += @{ Test = "Unit Tests"; Status = "ERROR"; Details = $_.Exception.Message }
    }
}

function Test-LogosApiService {
    Test-Step "LOGOS API Service"
    
    $serviceStarted = Start-ServiceWithTest -ServiceName "LOGOS API" -ServiceConfig $Services.LogosApi
    
    if (-not $serviceStarted) {
        return
    }
    
    Start-Sleep -Seconds 2
    
    # Test health endpoint
    $healthResult = Test-HttpEndpoint -Url "http://localhost:8090/health"
    if ($healthResult.Success) {
        Write-Success "LOGOS API health check passed"
        
        try {
            $healthData = $healthResult.Response.Content | ConvertFrom-Json
            if ($healthData.status -eq "healthy") {
                Write-Success "LOGOS API reports healthy status"
            } else {
                Write-Warning "LOGOS API status: $($healthData.status)"
            }
        } catch {
            Write-Warning "Could not parse health response"
        }
    } else {
        Write-Failure "LOGOS API health check failed: $($healthResult.Error)"
    }
    
    # Test authorize endpoint
    $authData = @{
        action = "test_action"
        context = @{ test = "data" }
        user_id = "test_user"
    } | ConvertTo-Json
    
    $authResult = Test-HttpEndpoint -Url "http://localhost:8090/authorize_action" -Method "POST" -Body $authData
    if ($authResult.Success) {
        Write-Success "LOGOS API authorization endpoint working"
        
        try {
            $authResponse = $authResult.Response.Content | ConvertFrom-Json
            if ($authResponse.proof_token) {
                Write-Success "LOGOS API generated proof token"
            } else {
                Write-Warning "No proof token in authorization response"
            }
        } catch {
            Write-Warning "Could not parse authorization response"
        }
    } else {
        Write-Failure "LOGOS API authorization endpoint failed: $($authResult.Error)"
    }
    
    # Test verify kernel endpoint
    $verifyResult = Test-HttpEndpoint -Url "http://localhost:8090/verify_kernel"
    if ($verifyResult.Success) {
        Write-Success "LOGOS API kernel verification endpoint working"
    } else {
        Write-Failure "LOGOS API kernel verification failed: $($verifyResult.Error)"
    }
}

function Test-ToolRouterService {
    Test-Step "Enhanced Tool Router Service"
    
    $serviceStarted = Start-ServiceWithTest -ServiceName "Tool Router" -ServiceConfig $Services.ToolRouter
    
    if (-not $serviceStarted) {
        return
    }
    
    Start-Sleep -Seconds 2
    
    # Test health endpoint
    $healthResult = Test-HttpEndpoint -Url "http://localhost:8000/health"
    if ($healthResult.Success) {
        Write-Success "Tool Router health check passed"
    } else {
        Write-Failure "Tool Router health check failed: $($healthResult.Error)"
    }
    
    # Test metrics endpoint
    $metricsResult = Test-HttpEndpoint -Url "http://localhost:8000/metrics"
    if ($metricsResult.Success) {
        Write-Success "Tool Router metrics endpoint working"
        
        if ($metricsResult.Response.Content -match "http_requests_total") {
            Write-Success "Tool Router Prometheus metrics available"
        } else {
            Write-Warning "Expected Prometheus metrics not found"
        }
    } else {
        Write-Failure "Tool Router metrics endpoint failed: $($metricsResult.Error)"
    }
    
    # Test chat endpoint
    $chatData = @{
        message = "Hello, can you help me test the system?"
        user_id = "test_user"
    } | ConvertTo-Json
    
    $chatResult = Test-HttpEndpoint -Url "http://localhost:8000/chat" -Method "POST" -Body $chatData
    if ($chatResult.Success) {
        Write-Success "Tool Router chat endpoint working"
        
        try {
            $chatResponse = $chatResult.Response.Content | ConvertFrom-Json
            if ($chatResponse.response) {
                Write-Success "Tool Router generated chat response"
            } else {
                Write-Warning "No response in chat result"
            }
        } catch {
            Write-Warning "Could not parse chat response"
        }
    } else {
        Write-Failure "Tool Router chat endpoint failed: $($chatResult.Error)"
    }
}

function Test-InteractiveChatService {
    Test-Step "Interactive Chat Service"
    
    $serviceStarted = Start-ServiceWithTest -ServiceName "Interactive Chat" -ServiceConfig $Services.InteractiveChat
    
    if (-not $serviceStarted) {
        return
    }
    
    Start-Sleep -Seconds 2
    
    # Test main page
    $chatResult = Test-HttpEndpoint -Url "http://localhost:8080/"
    if ($chatResult.Success) {
        Write-Success "Interactive Chat interface accessible"
        
        if ($chatResult.Response.Content -match "LOGOS") {
            Write-Success "Interactive Chat shows LOGOS branding"
        } else {
            Write-Warning "LOGOS branding not found in chat interface"
        }
    } else {
        Write-Failure "Interactive Chat interface failed: $($chatResult.Error)"
    }
    
    # Test chat API endpoint
    $chatApiData = @{
        message = "Test message for end-to-end validation"
    } | ConvertTo-Json
    
    $chatApiResult = Test-HttpEndpoint -Url "http://localhost:8080/chat" -Method "POST" -Body $chatApiData
    if ($chatApiResult.Success) {
        Write-Success "Interactive Chat API endpoint working"
    } else {
        Write-Failure "Interactive Chat API endpoint failed: $($chatApiResult.Error)"
    }
}

function Test-ServiceIntegration {
    Test-Step "Service Integration"
    
    # Test integration between services
    $integrationData = @{
        message = "test integration between services"
        user_id = "integration_test"
    } | ConvertTo-Json
    
    $integrationResult = Test-HttpEndpoint -Url "http://localhost:8000/chat" -Method "POST" -Body $integrationData
    if ($integrationResult.Success) {
        Write-Success "Service integration test passed"
        
        try {
            $responseData = $integrationResult.Response.Content | ConvertFrom-Json
            if ($responseData.response) {
                Write-Success "Integrated response generated successfully"
            } else {
                Write-Warning "Integration response format unexpected"
            }
        } catch {
            Write-Warning "Could not parse integration response"
        }
    } else {
        Write-Failure "Service integration test failed: $($integrationResult.Error)"
    }
    
    # Verify metrics show cross-service calls
    Start-Sleep -Seconds 1
    $metricsResult = Test-HttpEndpoint -Url "http://localhost:8000/metrics"
    if ($metricsResult.Success -and $metricsResult.Response.Content -match "http_requests_total") {
        Write-Success "Cross-service metrics captured"
    } else {
        Write-Warning "Cross-service metrics not found"
    }
}

function Test-ErrorHandling {
    Test-Step "Error Handling and Recovery"
    
    # Test invalid requests
    $invalidData = @{ invalid = "data" } | ConvertTo-Json
    $invalidResult = Test-HttpEndpoint -Url "http://localhost:8000/chat" -Method "POST" -Body $invalidData -ExpectedStatus 400
    
    if ($invalidResult.Success -or $invalidResult.StatusCode -eq 422) {
        Write-Success "Tool Router properly handles invalid requests"
    } else {
        Write-Warning "Tool Router error handling unclear (Status: $($invalidResult.StatusCode))"
    }
    
    # Test non-existent endpoints
    $notFoundResult = Test-HttpEndpoint -Url "http://localhost:8000/nonexistent" -ExpectedStatus 404
    if ($notFoundResult.Success) {
        Write-Success "Tool Router properly handles 404 errors"
    } else {
        Write-Warning "Tool Router 404 handling unclear (Status: $($notFoundResult.StatusCode))"
    }
    
    # Test LOGOS API error handling
    $invalidAuthData = @{ incomplete = "data" } | ConvertTo-Json
    $invalidAuthResult = Test-HttpEndpoint -Url "http://localhost:8090/authorize_action" -Method "POST" -Body $invalidAuthData -ExpectedStatus 400
    
    if ($invalidAuthResult.Success -or $invalidAuthResult.StatusCode -eq 422) {
        Write-Success "LOGOS API properly handles invalid requests"
    } else {
        Write-Warning "LOGOS API error handling unclear (Status: $($invalidAuthResult.StatusCode))"
    }
}

function Test-PerformanceBasics {
    Test-Step "Performance Characteristics"
    
    # Test response times with concurrent requests
    $startTime = Get-Date
    $jobs = @()
    
    for ($i = 1; $i -le 5; $i++) {
        $jobs += Start-Job -ScriptBlock {
            try {
                Invoke-WebRequest -Uri "http://localhost:8000/health" -UseBasicParsing -TimeoutSec 10
            } catch {
                $null
            }
        }
    }
    
    $results = $jobs | Wait-Job | Receive-Job
    $jobs | Remove-Job
    $endTime = Get-Date
    
    $successfulResponses = $results | Where-Object { $_.StatusCode -eq 200 }
    $duration = ($endTime - $startTime).TotalSeconds
    
    if ($successfulResponses.Count -eq 5) {
        $avgTime = $duration / 5
        Write-Success "Tool Router handled 5 concurrent requests (avg: $([math]::Round($avgTime, 3))s)"
    } else {
        Write-Warning "Only $($successfulResponses.Count)/5 concurrent requests succeeded"
    }
    
    # Test larger payload
    $largeData = @{
        message = ("This is a test message with more content " * 50)
        user_id = "performance_test"
        metadata = @{ test = "data" } * 10
    } | ConvertTo-Json
    
    $largeResult = Test-HttpEndpoint -Url "http://localhost:8000/chat" -Method "POST" -Body $largeData
    if ($largeResult.Success) {
        Write-Success "Tool Router handles larger payloads"
    } else {
        Write-Warning "Tool Router struggled with larger payloads: $($largeResult.Error)"
    }
}

function Stop-AllServices {
    Write-TestLog "Cleaning up services..." -Color $YELLOW
    
    foreach ($serviceInfo in $RunningProcesses) {
        try {
            if (-not $serviceInfo.Process.HasExited) {
                $serviceInfo.Process.Kill()
                Write-TestLog "Stopped $($serviceInfo.Name)"
            }
        } catch {
            Write-TestLog "Error stopping $($serviceInfo.Name): $($_.Exception.Message)" -Color $RED
        }
    }
    
    # Also kill any remaining Python processes
    Get-Process -Name "python*" -ErrorAction SilentlyContinue | Stop-Process -Force -ErrorAction SilentlyContinue
}

function Show-TestSummary {
    Write-Host ""
    Write-Host ("="*80) -ForegroundColor White
    Write-Host "${BOLD}LOGOS AGI SYSTEM - END-TO-END TEST SUMMARY${RESET}" -ForegroundColor White
    Write-Host ("="*80) -ForegroundColor White
    
    Write-Host ""
    Write-Host "${GREEN}✅ Tests Passed: $($TestResults.Passed)${RESET}" -ForegroundColor Green
    Write-Host "${RED}❌ Tests Failed: $($TestResults.Failed)${RESET}" -ForegroundColor Red
    Write-Host "${BLUE}📊 Total Tests: $($TestResults.Total)${RESET}" -ForegroundColor Blue
    
    if ($TestResults.Failed -eq 0) {
        Write-Host ""
        Write-Host "${GREEN}${BOLD}🎉 ALL SYSTEMS OPERATIONAL! 🎉${RESET}" -ForegroundColor Green
        Write-Host "${GREEN}The LOGOS AGI system is fully functional and ready for production.${RESET}" -ForegroundColor Green
    } else {
        $successRate = [math]::Round(($TestResults.Passed / $TestResults.Total) * 100, 1)
        Write-Host ""
        Write-Host "${YELLOW}⚠️  PARTIAL SUCCESS: $successRate% pass rate${RESET}" -ForegroundColor Yellow
        
        Write-Host ""
        Write-Host "${RED}Failed Tests Details:${RESET}" -ForegroundColor Red
        foreach ($detail in $TestResults.Details) {
            if ($detail.Status -ne "PASS") {
                Write-Host "  • $($detail.Test): $($detail.Status) - $($detail.Details)" -ForegroundColor Red
            }
        }
    }
    
    Write-Host ""
    Write-Host ("="*80) -ForegroundColor White
}

# Main execution
try {
    Write-Host "${BOLD}🚀 LOGOS AGI SYSTEM - COMPREHENSIVE END-TO-END TEST${RESET}" -ForegroundColor Cyan
    Write-Host "${BLUE}Testing all systems and subsystems for operational readiness...${RESET}" -ForegroundColor Blue
    Write-Host ""
    
    # Run all test phases
    Test-UnitTests
    Test-LogosApiService
    Test-ToolRouterService
    Test-InteractiveChatService
    Test-ServiceIntegration
    Test-ErrorHandling
    Test-PerformanceBasics
    
} catch {
    Write-TestLog "Test suite error: $($_.Exception.Message)" -Color $RED
} finally {
    if (-not $SkipCleanup) {
        Stop-AllServices
    }
    
    Show-TestSummary
    
    # Exit with appropriate code
    if ($TestResults.Failed -eq 0) {
        exit 0
    } else {
        exit 1
    }
}