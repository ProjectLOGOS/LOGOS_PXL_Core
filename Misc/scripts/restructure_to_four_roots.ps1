# Restructure repository into four root directories

# --- Create root directories ---
$roots = @("Three_Pillars_Corpus_Literature","PXL_IEL_overlay_system","LOGOS_AGI","Misc")
foreach ($r in $roots) { if (-not (Test-Path $r)) { New-Item -ItemType Directory -Force -Name $r | Out-Null } }

# --- 1. Three Pillars Corpus Literature (ZIP only) ---
if (Test-Path "8. 3 Pillars Corpus.zip") {
    Move-Item "8. 3 Pillars Corpus.zip" "Three_Pillars_Corpus_Literature" -Force
}

# --- 2. PXL / IEL overlay system ---
$pxl = @(
    "coq","examples","logos_core","pxl-prover","modules",
    "services","persistence","gateway","api","gui",
    "openapi","attested_io","third_party","extraction"
)
foreach ($item in $pxl) { if (Test-Path $item) { Move-Item $item "PXL_IEL_overlay_system" -Force } }

# --- 3. LOGOS AGI ---
# If there's a top-level LOGOS_AGI (and it's not the target dir), move its contents into the target
if (Test-Path "LOGOS_AGI") {
    $src = Get-Item -LiteralPath "LOGOS_AGI"
    $dest = Join-Path -Path (Get-Location) -ChildPath "LOGOS_AGI"
    # if source path and destination path resolve to the same object, do nothing
    if ($src.FullName -ne $dest) {
        Try {
            Move-Item -LiteralPath $src.FullName -Destination $dest -Force -ErrorAction Stop
        } Catch {
            Write-Host "Skipping move of LOGOS_AGI (would be a no-op or nested move): $($_.Exception.Message)"
        }
    }
}

# --- 4. Misc / Internal ---
$misc = @(
    ".githooks",".github",".vscode",".reuse","audit","charts","ci",
    "config","configs","deploy","metrics","monitoring","obdc","ops","out",
    "pilot","policies","reports","scripts","tests","tools",
    ".Makefile.*",".coq-sources",".env.example",".hasfile",".pre-commit-config.yaml"
)
foreach ($item in $misc) { 
    Get-ChildItem -Path . -Filter $item -Force -ErrorAction SilentlyContinue |
        ForEach-Object { Move-Item $_.FullName "Misc" -Force }
}

# --- Optional: keep top-level public docs ---
foreach ($f in @("README.md","RELEASE_NOTES.md")) { if (Test-Path $f) { Move-Item $f . -Force } }

# --- Git commit (optional) ---
if (Test-Path ".git") {
    git add .
    git commit -m "Restructured repo into 4 root directories: Three_Pillars_Corpus_Literature (ZIP only), PXL_IEL_overlay_system, LOGOS_AGI, and Misc"
}
