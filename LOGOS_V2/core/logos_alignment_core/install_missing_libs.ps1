#!/usr/bin/env pwsh
<#
.SYNOPSIS
    LOGOS Missing Libraries Installer
.DESCRIPTION
    Automates installation of missing Python libraries for LOGOS AGI
    Target: 11-13/13 libraries (84.6%-100%)
.NOTES
    Current Status: 11/13 (84.6%) ✅
    Missing: pymc (requires Python 3.10-3.12), pmdarima (requires VS Build Tools)
#>

Write-Host "=== LOGOS Library Installer ===" -ForegroundColor Cyan
Write-Host ""

# Check Python version
$pyVersion = python --version 2>&1
Write-Host "Python Version: $pyVersion" -ForegroundColor Yellow
Write-Host ""

# Current status check
Write-Host "=== Current Library Status ===" -ForegroundColor Cyan
python check_libraries.py
Write-Host ""

# Option 1: PyKalman (Already done if status shows 11/13)
Write-Host "`n[Option 1] PyKalman" -ForegroundColor Green
Write-Host "Status: Checking..." -ForegroundColor Yellow
python -c "import pykalman; print('  ✅ PyKalman already installed (version:', pykalman.__version__, ')')" 2>$null
if ($LASTEXITCODE -ne 0) {
    Write-Host "  ❌ Not installed. Installing..." -ForegroundColor Yellow
    pip install pykalman
    if ($LASTEXITCODE -eq 0) {
        Write-Host "  ✅ PyKalman installed successfully" -ForegroundColor Green
    } else {
        Write-Host "  ❌ PyKalman installation failed" -ForegroundColor Red
    }
} else {
    Write-Host "  ✅ Already installed" -ForegroundColor Green
}

# Option 2: pmdarima (Requires Build Tools)
Write-Host "`n[Option 2] pmdarima (Requires Visual Studio Build Tools)" -ForegroundColor Green
Write-Host "Checking for C++ compiler..." -ForegroundColor Yellow

# Check for Visual Studio Build Tools
$vsPaths = @(
    "C:\Program Files (x86)\Microsoft Visual Studio\2022\BuildTools\VC\Tools\MSVC",
    "C:\Program Files (x86)\Microsoft Visual Studio\2019\BuildTools\VC\Tools\MSVC",
    "C:\Program Files\Microsoft Visual Studio\2022\Community\VC\Tools\MSVC"
)

$vsFound = $false
foreach ($path in $vsPaths) {
    if (Test-Path $path) {
        Write-Host "  ✅ Visual Studio Build Tools found: $path" -ForegroundColor Green
        $vsFound = $true
        break
    }
}

if ($vsFound) {
    Write-Host "  Installing pmdarima..." -ForegroundColor Yellow
    pip install pmdarima
    if ($LASTEXITCODE -eq 0) {
        Write-Host "  ✅ pmdarima installed successfully" -ForegroundColor Green
        Write-Host "  🎉 Reached 12/13 libraries (92.3%)!" -ForegroundColor Cyan
    } else {
        Write-Host "  ❌ pmdarima installation failed (build error)" -ForegroundColor Red
        Write-Host "  💡 Alternative: Use statsmodels.tsa.arima instead" -ForegroundColor Yellow
    }
} else {
    Write-Host "  ⚠️  Visual Studio Build Tools not found" -ForegroundColor Yellow
    Write-Host ""
    Write-Host "  To install pmdarima, you need Visual Studio Build Tools:" -ForegroundColor Cyan
    Write-Host "  1. Download from: https://visualstudio.microsoft.com/downloads/#build-tools-for-visual-studio-2022" -ForegroundColor White
    Write-Host "  2. Run installer and select: 'Desktop development with C++'" -ForegroundColor White
    Write-Host "  3. Install (requires ~6.5 GB disk space, 15-30 min)" -ForegroundColor White
    Write-Host "  4. Restart terminal and run: pip install pmdarima" -ForegroundColor White
    Write-Host ""
    Write-Host "  💡 Alternative: Use statsmodels.tsa.arima (already installed)" -ForegroundColor Yellow
    Write-Host "     from statsmodels.tsa.arima.model import ARIMA" -ForegroundColor Gray
}

# Option 3: PyMC (Python version check)
Write-Host "`n[Option 3] PyMC (Requires Python 3.10-3.12)" -ForegroundColor Green

if ($pyVersion -match "3\.13") {
    Write-Host "  ⚠️  Python 3.13 detected - PyMC requires Python 3.10-3.12" -ForegroundColor Yellow
    Write-Host "  PyMC is installed but non-functional (missing pytensor)" -ForegroundColor Yellow
    Write-Host ""
    Write-Host "  Options:" -ForegroundColor Cyan
    Write-Host "  A) Use Pyro instead (already loaded, similar capabilities)" -ForegroundColor White
    Write-Host "  B) Create Python 3.12 virtual environment:" -ForegroundColor White
    Write-Host "     py -3.12 -m venv .venv312" -ForegroundColor Gray
    Write-Host "     .venv312\Scripts\Activate.ps1" -ForegroundColor Gray
    Write-Host "     pip install pymc pytensor" -ForegroundColor Gray
    Write-Host ""
    Write-Host "  💡 Recommended: Keep using Pyro (already working)" -ForegroundColor Yellow
} elseif ($pyVersion -match "3\.(10|11|12)") {
    Write-Host "  ✅ Compatible Python version detected" -ForegroundColor Green
    Write-Host "  Installing PyMC + pytensor..." -ForegroundColor Yellow
    pip install "pymc>=5.0" "pytensor>=2.18"
    if ($LASTEXITCODE -eq 0) {
        Write-Host "  ✅ PyMC installed successfully" -ForegroundColor Green
        Write-Host "  🎉 Reached 13/13 libraries (100%)!" -ForegroundColor Cyan
    } else {
        Write-Host "  ❌ PyMC installation failed" -ForegroundColor Red
    }
} else {
    Write-Host "  ⚠️  Unknown Python version: $pyVersion" -ForegroundColor Yellow
}

# Final status check
Write-Host "`n=== Final Library Status ===" -ForegroundColor Cyan
python check_libraries.py

# Summary
Write-Host "`n=== Installation Complete ===" -ForegroundColor Cyan

$finalCount = (python -c "import importlib; libs=['pyro','torch','sentence_transformers','networkx','arch','filterpy','pykalman','sklearn','speech_recognition','pyttsx3','tkinter','pymc','pmdarima']; loaded=[lib for lib in libs if importlib.util.find_spec(lib.replace('_',''))]; print(len(loaded))" 2>$null)

if ($finalCount -eq 11) {
    Write-Host "Status: 11/13 libraries (84.6%) ✅" -ForegroundColor Green
    Write-Host "Missing: pymc, pmdarima" -ForegroundColor Yellow
    Write-Host "System: OPERATIONAL with excellent coverage" -ForegroundColor Green
} elseif ($finalCount -eq 12) {
    Write-Host "Status: 12/13 libraries (92.3%) ✅✅" -ForegroundColor Green
    Write-Host "Missing: pymc" -ForegroundColor Yellow
    Write-Host "System: OPERATIONAL with outstanding coverage" -ForegroundColor Green
} elseif ($finalCount -eq 13) {
    Write-Host "Status: 13/13 libraries (100%) 🎉" -ForegroundColor Cyan
    Write-Host "System: FULLY OPERATIONAL" -ForegroundColor Green
} else {
    Write-Host "Status: $finalCount/13 libraries" -ForegroundColor Yellow
}

Write-Host "`nNext steps:" -ForegroundColor Cyan
Write-Host "  1. Test GUI: python gui.py" -ForegroundColor White
Write-Host "  2. Check logs: cat audit/gui_actions.log" -ForegroundColor White
Write-Host "  3. Read guide: LIBRARY_INSTALLATION_GUIDE.md" -ForegroundColor White
Write-Host ""
