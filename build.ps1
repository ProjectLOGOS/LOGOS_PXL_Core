# PowerShell build script for ChronoPraxis constructive core
param([switch]$Clean)

$chronoDir = "modules\chronopraxis"

if ($Clean) {
    Write-Host "Cleaning build artifacts..."
    Remove-Item "$chronoDir\*.vo" -ErrorAction SilentlyContinue
    Remove-Item "$chronoDir\*.vos" -ErrorAction SilentlyContinue  
    Remove-Item "$chronoDir\*.vok" -ErrorAction SilentlyContinue
    Remove-Item "$chronoDir\*.glob" -ErrorAction SilentlyContinue
    Write-Host "Clean complete."
    return
}

Write-Host "Building ChronoPraxis constructive core..."

# Set location to chronopraxis directory
Push-Location $chronoDir

try {
    # Build in dependency order
    $files = @(
        "ChronoAxioms.v",
        "Bijection.v", 
        "ChronoMappings.v",
        "ChronoTactics.v",
        "ChronoProofs.v",
        "ChronoPraxis.v",
        "SmokeTests.v"
    )
    
    foreach ($file in $files) {
        Write-Host "Compiling $file..."
        coqc $file
        if ($LASTEXITCODE -ne 0) {
            Write-Error "Failed to compile $file"
            exit 1
        }
    }
    
    Write-Host "Build complete! All modules compiled successfully."
    Write-Host "✅ ChronoPraxis constructive core is ready."
    
} finally {
    Pop-Location
}