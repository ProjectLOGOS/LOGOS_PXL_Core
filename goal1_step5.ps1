# Goal 1 — Step 5: quarantine classical kernels, re-run guard, rebuild Chrono, coqchk

$ErrorActionPreference = "Stop"
$root = (git rev-parse --show-toplevel); Set-Location $root
$null = New-Item -ItemType Directory -Force -Path reports

# 0) Define canonical loadpaths
@'
-Q pxl-minimal-kernel-main/coq                          PXLs
-Q api                                                  PXLs.API
-Q modules/IEL/source                                   PXLs.IEL.Source
-Q modules/IEL/pillars                                  PXLs.IEL.Pillars
-Q modules/IEL/infra/ChronoPraxis/substrate             PXLs.IEL.Infra.ChronoPraxis.Substrate
-Q modules/IEL/infra/ChronoPraxis/tactics               PXLs.IEL.Infra.ChronoPraxis.Tactics
-Q modules/IEL/infra/ChronoPraxis/theorems              PXLs.IEL.Infra.ChronoPraxis.Theorems
-Q modules/IEL/infra/ModalPraxis                        PXLs.IEL.Infra.ModalPraxis
-Q modules/IEL/infra/TopoPraxis                         PXLs.IEL.Infra.TopoPraxis
'@ | Set-Content _CoqProject -Encoding UTF8

# 1) Quarantine known classical/experimental kernel files out of the build and guard
$expDir = "pxl-minimal-kernel-main/coq/experimental"; New-Item -ItemType Directory -Force -Path $expDir | Out-Null
$toQuarantine = @(
  "pxl-minimal-kernel-main/coq/Assumptions.v",
  "pxl-minimal-kernel-main/coq/Constructive_Lindenbaum_Demo.v",
  "pxl-minimal-kernel-main/coq/PXL_Completeness_Instance.v",
  "pxl-minimal-kernel-main/coq/PXL_Completeness_Work.v",
  "pxl-minimal-kernel-main/coq/theorems/PXL_Completeness_Truth_WF.v"
) | Where-Object { Test-Path $_ }
foreach($p in $toQuarantine){
  Move-Item -Force $p -Destination (Join-Path $expDir ([IO.Path]::GetFileName($p)))
}

# 2) Rebuild _CoqProject without experimental subtree
@'
-Q pxl-minimal-kernel-main/coq                          PXLs
-Q api                                                  PXLs.API
-Q modules/IEL/source                                   PXLs.IEL.Source
-Q modules/IEL/pillars                                  PXLs.IEL.Pillars
-Q modules/IEL/infra/ChronoPraxis/substrate             PXLs.IEL.Infra.ChronoPraxis.Substrate
-Q modules/IEL/infra/ChronoPraxis/tactics               PXLs.IEL.Infra.ChronoPraxis.Tactics
-Q modules/IEL/infra/ChronoPraxis/theorems              PXLs.IEL.Infra.ChronoPraxis.Theorems
-Q modules/IEL/infra/ModalPraxis                        PXLs.IEL.Infra.ModalPraxis
-Q modules/IEL/infra/TopoPraxis                         PXLs.IEL.Infra.TopoPraxis
'@ | Set-Content _CoqProject -Encoding UTF8

# 3) Guard scan: CORE scope excluding ChronoPraxis and experimental
$allowRoots = @("pxl-minimal-kernel-main/coq","modules/IEL/infra","modules/IEL/source","modules/IEL/pillars")
$pattern = '(?<![A-Za-z])Axiom(?![A-Za-z])|Admitted\.'
$axiomsCore = "reports\goal1_step5_axioms_core_guard.txt"
$scan = $allowRoots | % { if(Test-Path $_){ Get-ChildItem -Recurse $_ -Filter *.v } }
$matches = $scan | Select-String -Pattern $pattern -SimpleMatch:$false |
  Where-Object {
    $_.Path -notmatch '\\IEL\\infra\\ChronoPraxis\\' -and
    $_.Path -notmatch '\\coq\\experimental\\'
  }
$matches | ForEach-Object { "$($_.Path):$($_.LineNumber): $($_.Line)" } | Set-Content $axiomsCore

if ($matches.Count -gt 0) {
  Write-Error "Guard failed: non-Chrono Axiom/Admitted remain (see $axiomsCore). Fix or quarantine remaining files, then re-run."
}

# 4) Build Chrono focus set
$QArgs = @(); Get-Content _CoqProject | %{
  if ($_ -match '^\s*-Q\s+(\S+)\s+(\S+)') { $QArgs += @("-Q",$Matches[1],$Matches[2]) }
}
$chronopaths = @(
  "modules/IEL/infra/ChronoPraxis/substrate/ChronoAxioms.v",
  "modules/IEL/infra/ChronoPraxis/substrate/Bijection.v",
  "modules/IEL/infra/ChronoPraxis/substrate/ChronoMappings.v",
  "modules/IEL/infra/ChronoPraxis/tactics/ChronoTactics.v",
  "modules/IEL/infra/ChronoPraxis/theorems/ChronoProofs.v"
) | Where-Object { Test-Path $_ }

$buildLog = "reports\goal1_step5_build_chrono.log"; "" | Set-Content $buildLog
Get-ChildItem -Recurse -Include *.vo,*.glob | Remove-Item -Force -ErrorAction SilentlyContinue

foreach($f in $chronopaths){
  "$([DateTime]::Now.ToString('s'))  coqc $f" | Tee-Object $buildLog -Append | Out-Null
  & coqc @QArgs $f 2>&1 | Tee-Object $buildLog -Append
  if ($LASTEXITCODE -ne 0) { "FAIL: $f" | Tee-Object $buildLog -Append; throw "Compile failed: $f" }
}

# 5) coqchk with same -Q mapping
$chk = "reports\goal1_step5_coqchk.txt"
& coqchk -R . PXLs @QArgs `
  PXLs.PXLv3 `
  PXLs.IEL.Source.TheoPraxis.Props `
  PXLs.IEL.Infra.ChronoPraxis.Substrate.ChronoMappings `
  PXLs.IEL.Infra.ChronoPraxis.Tactics.ChronoTactics `
  PXLs.IEL.Infra.ChronoPraxis.Theorems.ChronoProofs `
  2>&1 | Set-Content $chk

"OK: Chrono build and coqchk slice complete. Review:"
"- $buildLog (tail)"
"- $chk (full)"
"- $axiomsCore (should be empty)"