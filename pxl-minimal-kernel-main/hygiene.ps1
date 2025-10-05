$paths = Get-Content _CoqProject.minimal | Where-Object {$_ -notmatch '^\s*$' -and $_ -notmatch '^-' }
$files = $paths | ForEach-Object { $_.Trim() } | Get-ChildItem
$bad = $files | Select-String -Pattern '\bAdmitted\b|\bAxiom\b|\bParameter\b'
# Allow Axiom in Assumptions.v as quarantined
$bad = $bad | Where-Object { -not ($_.Filename -eq 'Assumptions.v' -and $_.Line -match '\bAxiom\b') }
if ($bad) {
  $bad | ForEach-Object { "{0}:{1}  {2}" -f $_.Filename, $_.LineNumber, $_.Line.Trim() } |
    Tee-Object -FilePath hygiene.txt
  throw "Placeholders detected in minimal kernel."
}
"OK" | Tee-Object -FilePath hygiene.txt
