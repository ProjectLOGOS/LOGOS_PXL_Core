# Goal 1 — Step 4: fix ChronoMappings import, hard-fail on leaks, valid coqchk

$ErrorActionPreference = "Stop"
$root = (git rev-parse --show-toplevel); Set-Location $root
$null = New-Item -ItemType Directory -Force -Path reports

# 0) Canonical loadpath
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

# 1) One-shot auto-fix for common bad logical paths in Chrono files
$fixes = @(
  @{Path="modules/IEL/infra/ChronoPraxis/substrate/ChronoMappings.v"; Find="Require Import ChronoAxioms";        Rep="From PXLs.IEL.Infra.ChronoPraxis.Substrate Require Import ChronoAxioms."},
  @{Path="modules/IEL/infra/ChronoPraxis/substrate/ChronoMappings.v"; Find="Require Import Bijection";           Rep="From PXLs.IEL.Infra.ChronoPraxis.Substrate Require Import Bijection."},
  @{Path="modules/IEL/infra/ChronoPraxis/tactics/ChronoTactics.v";   Find="Require Import Bijection";           Rep="From PXLs.IEL.Infra.ChronoPraxis.Substrate Require Import Bijection."},
  @{Path="modules/IEL/infra/ChronoPraxis/theorems/ChronoProofs.v";   Find="Require Import ChronoAxioms";        Rep="From PXLs.IEL.Infra.ChronoPraxis.Substrate Require Import ChronoAxioms."},
  @{Path="modules/IEL/infra/ChronoPraxis/theorems/ChronoProofs.v";   Find="Require Import ChronoMappings";      Rep="From PXLs.IEL.Infra.ChronoPraxis.Substrate Require Import ChronoMappings."}
)
foreach($f in $fixes){
  if(Test-Path $f.Path){
    (Get-Content $f.Path -Raw) -replace [regex]::Escape($f.Find), $f.Rep | Set-Content $f.Path -Encoding UTF8
  }
}

# 2) Re-scan Chrono subtree for Axiom/Admitted
$chronopaths = @(
  "modules/IEL/infra/ChronoPraxis/substrate/ChronoAxioms.v",
  "modules/IEL/infra/ChronoPraxis/substrate/Bijection.v",
  "modules/IEL/infra/ChronoPraxis/substrate/ChronoMappings.v",
  "modules/IEL/infra/ChronoPraxis/tactics/ChronoTactics.v",
  "modules/IEL/infra/ChronoPraxis/theorems/ChronoProofs.v"
) | Where-Object { Test-Path $_ }

$axiomsChrono = "reports\goal1_step4_axioms_chrono.txt"
$pattern = '(?<![A-Za-z])Axiom(?![A-Za-z])|Admitted\.'
$chronopaths | Select-String -Pattern $pattern -SimpleMatch:$false |
  ForEach-Object { "$($_.Path):$($_.LineNumber): $($_.Line)" } |
  Set-Content $axiomsChrono

# 3) Guard: fail if any Axiom/Admitted outside Chrono in CORE scope
$allowRoots = @(
  "pxl-minimal-kernel-main/coq",
  "modules/IEL/infra",
  "modules/IEL/source",
  "modules/IEL/pillars"
)
$scan = $allowRoots | % { if(Test-Path $_){ Get-ChildItem -Recurse $_ -Filter *.v } }
$axiomsCore = "reports\goal1_step4_axioms_core_guard.txt"
$scan | Select-String -Pattern $pattern -SimpleMatch:$false |
  Where-Object { $_.Path -notmatch '\\ChronoPraxis\\' } |
  ForEach-Object { "$($_.Path):$($_.LineNumber): $($_.Line)" } |
  Set-Content $axiomsCore

if ((Get-Content $axiomsCore | Measure-Object -Line).Lines -gt 0) {
  Write-Error "Guard failed: non-Chrono Axiom/Admitted present. See $axiomsCore"
}

# 4) Clean and compile Chrono focus set
$QArgs = @(); Get-Content _CoqProject | %{
  if ($_ -match '^\s*-Q\s+(\S+)\s+(\S+)') { $QArgs += @("-Q",$Matches[1],$Matches[2]) }
}
$log = "reports\goal1_step4_build_chrono.log"; "" | Set-Content $log
Get-ChildItem -Recurse -Include *.vo,*.glob | Remove-Item -Force -ErrorAction SilentlyContinue

foreach($f in $chronopaths){
  "$([DateTime]::Now.ToString('s'))  coqc $f" | Tee-Object $log -Append | Out-Null
  & coqc @QArgs $f 2>&1 | Tee-Object $log -Append
  if ($LASTEXITCODE -ne 0) { "FAIL: $f" | Tee-Object $log -Append; throw "Compile failed: $f" }
}

# 5) coqchk on validated slice (no -quiet; Coq 8.20 coqchk rejects it)
$chk = "reports\goal1_step4_coqchk.txt"
& coqchk -R . PXLs `
  PXLs.PXLv3 `
  PXLs.IEL.Source.TheoPraxis.Props `
  PXLs.IEL.Infra.ChronoPraxis.Substrate.ChronoMappings `
  PXLs.IEL.Infra.ChronoPraxis.Tactics.ChronoTactics `
  PXLs.IEL.Infra.ChronoPraxis.Theorems.ChronoProofs `
  2>&1 | Set-Content $chk

"Done. Return:"
"- last 80 lines of $log"
"- first 80 lines of $axiomsChrono"
"- full $chk"