# scripts/build.ps1
$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location (Resolve-Path "$root\..")

# Collect .v files under modules/IEL, api, pxl-minimal-kernel-main/coq, tests, examples
$files = Get-ChildItem -Recurse -Filter *.v | Where-Object { $_.FullName -notlike "*\node_modules\*" -and $_.FullName -notlike "*\.git\*" } | % { $_.FullName }

# Produce dependencies with coqdep (Windows-safe)
$coqargs = @("-Q", "pxl-minimal-kernel-main/coq", "PXLs", "-Q", "modules/IEL/source", "PXLs.IEL.Source", "-Q", "modules/IEL/infra", "PXLs.IEL.Infra", "-Q", "modules/IEL/pillars", "PXLs.IEL.Pillars", "-Q", "modules/IEL/experimental", "PXLs.IEL.Experimental", "-Q", "tests", "tests", "-Q", "api", "PXLs.API")
$dep = & coqdep $coqargs $files 2>$null

# Parse coqdep format: "path\file.vo: dep1.vo dep2.vo ..."
# Build a DAG and topo-sort
$dag = @{}
$rev = @{}
foreach ($line in $dep) {
  if ($line -notmatch "^(.*)\.vo: (.*)$") { continue }
  $t = $Matches[1].Replace('/', '\')
  $deps = @()
  foreach ($d in $Matches[2].Split(' ', [System.StringSplitOptions]::RemoveEmptyEntries)) {
    if ($d -match "^(.*)\.vo$") { $deps += $Matches[1].Replace('/', '\') }
  }
  $dag[$t] = $deps
  foreach ($d in $deps) { if (-not $rev.ContainsKey($d)) { $rev[$d] = @() }; $rev[$d] += $t }
}

# Kahn topo
$S = New-Object System.Collections.Generic.Queue[System.String]
$ind = @{}
foreach ($n in $dag.Keys) { $ind[$n] = $dag[$n].Count }
foreach ($n in $dag.Keys) { if ($ind[$n] -eq 0) { $S.Enqueue($n) } }
$order = @()
while ($S.Count -gt 0) {
  $n = $S.Dequeue()
  $order += $n
  if ($rev.ContainsKey($n)) {
    foreach ($m in $rev[$n]) {
      $ind[$m]--
      if ($ind[$m] -eq 0) { $S.Enqueue($m) }
    }
  }
}

# Compile in order (replace .vo with .v to get source path)
foreach ($vo in $order) {
  $v = ($vo -replace '\.vo$','.v')
  $src = Get-ChildItem -Recurse -Filter (Split-Path $v -Leaf) | Select-Object -First 1
  if ($null -ne $src) {
    & coqc -q $coqargs $src.FullName
  }
}

# Kernel check
& coqchk -R . PXLs
Write-Host "Build OK"