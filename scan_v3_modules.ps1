# CONFIG
$root = 'C:\Users\proje\OneDrive\Desktop\LOGOS SYSTEM\v3'
$report = 'C:\Users\proje\OneDrive\Desktop\Project_Directory\LOGOS_PXL_Core\reports\v3_scan_hits.tsv'
$patterns = @(
  'G(ö|o)delian.*Desire.*Driver',
  'Trinitarian.*Axiom.*Choice',
  'causal.*simulat',            # causal simulator
  'recursive.*goal',
  'goal\s*engine',
  'planner',
  'workflow',
  'hyper[\- ]node'
)

# SEARCH
Get-ChildItem -Path $root -Recurse -File -Include *.v,*.ml,*.mli,*.py,*.ts,*.tsx,*.md,*.txt |
  Select-String -Pattern $patterns -AllMatches -CaseSensitive:$false |
  Sort-Object Path, LineNumber |
  Select-Object @{n='Path';e={$_.Path}},
                @{n='Line';e={$_.LineNumber}},
                @{n='Text';e={$_.Line.Trim()}} |
  Tee-Object -FilePath $report | Format-Table -Auto