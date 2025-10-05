param([string]$PXLRepo)
if(-not $PXLRepo){ Write-Error "Usage: .\ci\pin_kernel_hash.ps1 -PXLRepo C:\path\pxl"; exit 1 }
$vo = Get-ChildItem -Recurse -Filter *.vo -Path $PXLRepo
if(-not $vo){ throw "No .vo files. Build PXL first." }
$hashes = foreach($f in ($vo | Sort-Object FullName)){ (Get-FileHash $f.FullName -Algorithm SHA256).Hash }
$text = ($hashes -join "`n")
$sha256 = [System.Security.Cryptography.SHA256]::Create()
$bytes = [System.Text.Encoding]::UTF8.GetBytes($text)
$kernelHash = ($sha256.ComputeHash($bytes) | ForEach-Object ToString X2) -join ""
$cfg = Get-Content configs/config.json | ConvertFrom-Json
$cfg.expected_kernel_hash = $kernelHash
$cfg | ConvertTo-Json -Depth 6 | Set-Content configs/config.json -Encoding UTF8
Write-Host "Pinned kernel hash:" $kernelHash
