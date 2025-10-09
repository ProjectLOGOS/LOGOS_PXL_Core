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

# Coq compile all .v files
Write-Host "Compiling Coq files..."
Get-ChildItem -Recurse -Filter *.v | Where-Object { $_.FullName -notlike "*\api\*" -and $_.FullName -notlike "*pxl-minimal-kernel-main*" } | ForEach-Object {
    $coqcCmd = "coqc -Q pxl-minimal-kernel-main/coq PXLs -Q modules/IEL/source PXLs.IEL.Source -Q modules/IEL/infra PXLs.IEL.Infra -Q modules/IEL/infra/ChronoPraxis PXLs.IEL.Infra.ChronoPraxis -Q modules/IEL/infra/ChronoPraxis/substrate PXLs.IEL.Infra.ChronoPraxis.Substrate -Q modules/IEL/infra/ModalPraxis PXLs.IEL.Infra.ModalPraxis -Q modules/IEL/infra/TropoPraxis PXLs.IEL.Infra.TropoPraxis -Q modules/IEL/pillars PXLs.IEL.Pillars -Q modules/IEL/experimental PXLs.IEL.Experimental -Q tests tests $($_.FullName)"
    Write-Host "Running: $coqcCmd"
    Invoke-Expression $coqcCmd
    if ($LASTEXITCODE -ne 0) {
        Write-Error "Coq compilation failed for $($_.FullName)"
        exit 1
    }
}

# Coq kernel check
Write-Host "Running coqchk..."
coqchk -Q pxl-minimal-kernel-main/coq PXLs -Q modules/IEL/source PXLs.IEL.Source -Q modules/IEL/infra PXLs.IEL.Infra -Q modules/IEL/infra/ChronoPraxis PXLs.IEL.Infra.ChronoPraxis -Q modules/IEL/infra/ChronoPraxis/substrate PXLs.IEL.Infra.ChronoPraxis.Substrate -Q modules/IEL/infra/ModalPraxis PXLs.IEL.Infra.ModalPraxis -Q modules/IEL/infra/TropoPraxis PXLs.IEL.Infra.TropoPraxis -Q modules/IEL/pillars PXLs.IEL.Pillars -Q modules/IEL/experimental PXLs.IEL.Experimental -Q tests tests
if ($LASTEXITCODE -ne 0) {
    Write-Error "coqchk failed"
    exit 1
}

Write-Host "Build successful!"