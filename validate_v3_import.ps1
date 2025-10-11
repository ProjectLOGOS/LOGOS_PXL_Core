# Build checks after V3 import
# From repo root

# Build the project
Write-Host "Building Coq project..."
pwsh ./build.ps1

# Run coqchk on verified slice
Write-Host "Running coqchk verification..."
coqchk -R . PXLs PXLs.PXLv3

# Check for Axiom/Admitted in vendor code
Write-Host "Scanning for Axiom/Admitted in vendor directories..."
Get-ChildItem -Path third_party/logos_agi_v4_local -Recurse -File -Include *.v |
  Select-String -Pattern "(^Axiom\b|Admitted\.)" -AllMatches -CaseSensitive:$false

Write-Host "Build validation complete."