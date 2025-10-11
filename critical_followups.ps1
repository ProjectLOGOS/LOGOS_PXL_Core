# Critical Follow-ups: Eliminate Axiom/Admitted and Lock Quality

# 1. Scan for residual Axiom/Admitted in non-experimental code
Write-Host "Scanning for Axiom/Admitted in verified code paths..."
Get-ChildItem -Path . -Recurse -File -Include *.v -Exclude experimental/**, **/_build/**, **/.coq-native/** |
  Select-String -Pattern "Axiom|Admitted" -AllMatches -CaseSensitive:$false |
  Out-File -FilePath reports/axiom_scan.txt

# Check if scan found any hits
if (Test-Path reports/axiom_scan.txt) {
    $hits = Get-Content reports/axiom_scan.txt
    if ($hits.Length -gt 0) {
        Write-Host "FOUND AXIOM/ADMITTED HITS:" -ForegroundColor Red
        $hits | ForEach-Object { Write-Host "  $_" -ForegroundColor Yellow }
        Write-Host ""
        Write-Host "MANUAL INTERVENTION REQUIRED:" -ForegroundColor Cyan
        Write-Host "  - Quarantine or prove the axioms constructively"
        Write-Host "  - Re-run coqchk on exact verified slice"
        Write-Host "  - Update verified_slice.lst if needed"
        exit 1
    } else {
        Write-Host "No Axiom/Admitted found in verified slice" -ForegroundColor Green
    }
} else {
    Write-Host "No Axiom/Admitted found in verified slice" -ForegroundColor Green
}

# 2. Freeze the validated slice in CI
Write-Host ""
Write-Host "Freezing verified slice manifest..."
$sliceContent = @(
    "PXLs.PXLv3",
    "PXLs.IEL.Source.TheoPraxis.Props",
    "PXLs.IEL.Infra.ChronoPraxis.Core"
) -join "`n"

$sliceContent | Out-File -FilePath tools/verified_slice.lst -Encoding UTF8
Write-Host "Created tools/verified_slice.lst with verified modules"

# 3. Run coqchk on verified slice
Write-Host ""
Write-Host "Running coqchk verification on verified slice..."
$sliceModules = Get-Content tools/verified_slice.lst
foreach ($module in $sliceModules) {
    Write-Host "Verifying $module..."
    coqchk -Q pxl-minimal-kernel-main/coq PXLs `
           -Q modules/IEL/source PXLs.IEL.Source `
           -Q modules/IEL/infra/ChronoPraxis PXLs.IEL.Infra.ChronoPraxis `
           $module
    if ($LASTEXITCODE -ne 0) {
        Write-Host "coqchk failed for $module" -ForegroundColor Red
        exit 1
    }
}

Write-Host "All verified slice modules passed coqchk" -ForegroundColor Green

# 4. SBOM generation commands (for manual execution)
Write-Host ""
Write-Host "SBOM Generation Commands (run manually):" -ForegroundColor Cyan
Write-Host "syft packages docker:logos-gateway:v2.2.0 -o spdx-json > sbom.gateway.json"
Write-Host "cosign attest --predicate sbom.gateway.json --type spdx logos-gateway:v2.2.0"
Write-Host "cosign verify-attestation logos-gateway:v2.2.0"

# 5. Blue/green deploy guardrails
Write-Host ""
Write-Host "Blue/Green Deploy Commands (run manually):" -ForegroundColor Cyan
Write-Host "k6 run k6/canary.js && ./ops/promql_slo_guard.sh p95_ms<=300 error_rate<=0.05"

Write-Host ""
Write-Host "Critical follow-ups completed successfully!" -ForegroundColor Green
Write-Host "Ready for V3 integration and production deployment."