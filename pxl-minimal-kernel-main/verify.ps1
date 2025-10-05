Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'
$root = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location $root

Write-Host "== Clean artifacts =="
Get-ChildItem -Recurse -Include *.vo,*.vok,*.vos | Remove-Item -Force -ErrorAction SilentlyContinue

Write-Host "== Generate minimal Makefile =="
coq_makefile -f _CoqProject.minimal -o Makefile.min

Write-Host "== Build minimal kernel =="
make -f Makefile.min clean all

Write-Host "== Kernel check =="
coqchk -R . PXLs

Write-Host "== Hygiene check =="
powershell -NoProfile -ExecutionPolicy Bypass -File .\hygiene.ps1

Write-Host "== Done =="
