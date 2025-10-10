# Goal 1 — Step 6: enforce constructive Chrono, rebuild, coqchk
$ErrorActionPreference="Stop"
$root = (git rev-parse --show-toplevel); Set-Location $root
$null = New-Item -ItemType Directory -Force -Path reports

# Scan Chrono only
$chronoroot = "modules/IEL/infra/ChronoPraxis"
$pat = '(?<![A-Za-z])Axiom(?![A-Za-z])|Admitted\.'
$ax = "reports/goal1_step6_axioms_chrono_guard.txt"
$results = Get-ChildItem -Recurse $chronoroot -Filter *.v |
  Where-Object { $_.FullName -notlike '*experimental*' } |
  Select-String -Pattern $pat -SimpleMatch:$false
$results | ForEach-Object { "$($_.Path):$($_.LineNumber): $($_.Line)" } | Set-Content $ax
if ($results.Count -gt 0) {
  Write-Error "Chrono still has Axiom/Admitted (see $ax)."
}

# Rebuild Chrono focus set
$QArgs=@(); Get-Content _CoqProject | %{
  if ($_ -match '^\s*-Q\s+(\S+)\s+(\S+)') { $QArgs += @("-Q",$Matches[1],$Matches[2]) }
}
$targets = @(
  "modules/IEL/infra/ChronoPraxis/substrate/ChronoAxioms.v",
  "modules/IEL/infra/ChronoPraxis/substrate/Bijection.v",
  "modules/IEL/infra/ChronoPraxis/substrate/ChronoMappings.v",
  "modules/IEL/infra/ChronoPraxis/tactics/ChronoTactics.v",
  "modules/IEL/infra/ChronoPraxis/theorems/ChronoProofs.v"
) | ? { Test-Path $_ }

$log="reports/goal1_step6_build_chrono.log"; "" | Set-Content $log
Get-ChildItem -Recurse -Include *.vo,*.glob | Remove-Item -Force -ErrorAction SilentlyContinue
foreach($f in $targets){
  "$([DateTime]::Now.ToString('s'))  coqc $f" | Tee-Object $log -Append | Out-Null
  & coqc @QArgs $f 2>&1 | Tee-Object $log -Append
  if ($LASTEXITCODE -ne 0) { "FAIL: $f" | Tee-Object $log -Append; throw "Compile failed: $f" }
}

# coqchk slice
$chk="reports/goal1_step6_coqchk.txt"
& coqchk @QArgs `
  PXLs.PXLv3 `
  PXLs.IEL.Source.TheoPraxis.Props `
  PXLs.IEL.Infra.ChronoPraxis.Substrate.ChronoMappings `
  PXLs.IEL.Infra.ChronoPraxis.Tactics.ChronoTactics `
  PXLs.IEL.Infra.ChronoPraxis.Theorems.ChronoProofs `
  2>&1 | Set-Content $chk

"OK: Step 6 complete. Inspect:"
$log; $ax; $chk