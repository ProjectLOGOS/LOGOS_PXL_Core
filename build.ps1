# LOGOS PXL Core Build Script (Windows PowerShell)
# Constructive axiom elimination and coqchk verification
param([switch]$Clean)

if ($Clean) {
    Write-Host "Cleaning build artifacts..."
    Get-ChildItem -Recurse -Include *.vo, *.vos, *.vok, *.glob | Remove-Item -ErrorAction SilentlyContinue
    Write-Host "Clean complete."
    return
}

Write-Host "Starting LOGOS PXL Core build..."

# Activate virtual environment if exists
if (Test-Path ".venv\Scripts\Activate.ps1") {
    & .venv\Scripts\Activate.ps1
}

# Coq compile all .v files in dependency order
Write-Host "Compiling Coq files..."

# First compile the PXL kernel
Write-Host "Compiling PXL kernel..."
$coqcCmd = "coqc -Q pxl-minimal-kernel-main/coq PXLs `"pxl-minimal-kernel-main/coq/PXLv3.v`""
Write-Host "Running: $coqcCmd"
Invoke-Expression $coqcCmd
if ($LASTEXITCODE -ne 0) {
    Write-Error "Coq compilation failed for PXLv3.v"
    exit 1
}

$compileOrder = @(
    "modules/IEL/source",
    "modules/IEL/infra/ChronoPraxis/substrate",
    "modules/IEL/infra",
    "modules/IEL/pillars",
    "modules/IEL/experimental",
    "examples",
    "LOGOS_AGI/proofs",
    "tests"
)

foreach ($dir in $compileOrder) {
    if (Test-Path $dir) {
        Get-ChildItem -Path $dir -Recurse -Filter *.v | Where-Object { $_.FullName -notlike "*\api\*" -and $_.FullName -notlike "*pxl-minimal-kernel-main*" } | Sort-Object { if ($_.Name -eq 'Spec.v') { 0 } else { -($_.FullName -split '\\').Count } }, FullName | ForEach-Object {
            $coqcCmd = "coqc -Q pxl-minimal-kernel-main/coq PXLs -Q modules/IEL/infra/ChronoPraxis/Theorems/experimental PXLs.IEL.Infra.ChronoPraxis.Theorems.experimental -Q modules/IEL/infra/ChronoPraxis/Theorems/experimental ChronoState -Q modules/IEL/source PXLs.IEL.Source -Q modules/IEL/source/TheoPraxis/subdomains PXLs.IEL.Source.TheoPraxis.subdomains -Q modules/IEL/source/TheoPraxis/subdomains/Unity PXLs.IEL.Source.TheoPraxis.subdomains.Unity -Q modules/IEL/pillars PXLs.IEL.Pillars -Q modules/IEL/infra/ModalPraxis PXLs.IEL.Infra.ModalPraxis -Q modules/IEL/infra/ChronoPraxis PXLs.IEL.Infra.ChronoPraxis -Q modules/IEL/infra/TopoPraxis PXLs.IEL.Infra.TopoPraxis `"$($_.FullName)`""
            Write-Host "Running: $coqcCmd"
            Invoke-Expression $coqcCmd
            if ($LASTEXITCODE -ne 0) {
                Write-Error "Coq compilation failed for $($_.FullName)"
                exit 1
            }
        }
    }
}

# Coq kernel check
Write-Host "Running coqchk..."
coqchk -Q pxl-minimal-kernel-main/coq PXLs -Q modules/IEL/infra/ChronoPraxis/Theorems/experimental PXLs.IEL.Infra.ChronoPraxis.Theorems.experimental -Q modules/IEL/infra/ChronoPraxis/Theorems/experimental ChronoState -Q modules/IEL/source PXLs.IEL.Source -Q modules/IEL/source/TheoPraxis/subdomains PXLs.IEL.Source.TheoPraxis.subdomains -Q modules/IEL/source/TheoPraxis/subdomains/Unity PXLs.IEL.Source.TheoPraxis.subdomains.Unity -Q modules/IEL/infra PXLs.IEL.Infra -Q modules/IEL/infra/ChronoPraxis PXLs.IEL.Infra.ChronoPraxis -Q modules/IEL/infra/ChronoPraxis/substrate PXLs.IEL.Infra.ChronoPraxis.Substrate -Q modules/IEL/infra/ModalPraxis PXLs.IEL.Infra.ModalPraxis -Q modules/IEL/infra/TropoPraxis PXLs.IEL.Infra.TropoPraxis -Q modules/IEL/pillars PXLs.IEL.Pillars -Q modules/IEL/experimental PXLs.IEL.Experimental -Q tests tests
if ($LASTEXITCODE -ne 0) {
    Write-Error "coqchk failed"
    exit 1
}

Write-Host "Build successful!"