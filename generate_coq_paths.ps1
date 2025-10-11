$dest = 'C:\Users\proje\OneDrive\Desktop\Project_Directory\LOGOS_PXL_Core\third_party\logos_agi_v4_local'

$coqDirs = Get-ChildItem $dest -Recurse -Filter *.v | ForEach-Object { Split-Path $_.FullName -Parent } | Sort-Object -Unique

"_CoqProject entries to add:"
$coqDirs | ForEach-Object { '-Q ' + $_ + ' PXLs.V4' }