# LOGOS Library Installation Guide
## Getting to 11-13/13 Libraries (84.6%-100%)

**Current Status:** 10/13 (76.9%)  
**Target:** 11-13/13 (84.6%-100%)  
**Date:** October 25, 2025

---

## Missing Libraries Analysis

### 1. PyKalman ✅ EASY FIX
**Status:** Not installed  
**Impact:** Advanced Kalman filtering  
**Solution:** Simple pip install  
**Difficulty:** ⭐ (5 minutes)

```powershell
pip install pykalman
```

**Why it's missing:** Was in requirements.txt but install may have been skipped  
**Fallback:** FilterPy provides similar functionality (already loaded)

---

### 2. PyMC ⚠️ PYTHON VERSION ISSUE
**Status:** Installed but non-functional (missing pytensor dependency)  
**Impact:** Bayesian modeling and probabilistic programming  
**Solution:** Requires Python 3.10-3.12 OR skip  
**Difficulty:** ⭐⭐⭐⭐ (requires Python downgrade or complex workaround)

#### Problem:
- PyMC 5.10.4 is installed
- Requires `pytensor` 2.18.1-2.25.x
- ALL pytensor versions require Python <3.13
- Current Python: 3.13.9 (incompatible)

#### Solutions:

**Option A: Accept Current State (RECOMMENDED)**
- Keep using Pyro (already loaded, similar capabilities)
- Document PyMC as "Requires Python 3.10-3.12"
- Stays at 10/13 libraries

**Option B: Python Downgrade (Advanced)**
1. Install Python 3.12.x from https://python.org
2. Create new virtual environment:
   ```powershell
   py -3.12 -m venv .venv312
   .venv312\Scripts\Activate.ps1
   pip install -r requirements.txt
   ```
3. Reinstall all packages
4. Update gui.py shebang to use Python 3.12

**Option C: Conditional Import (Temporary)**
```python
try:
    import pymc
    HAS_PYMC = True
except ImportError:
    HAS_PYMC = False
    # Use Pyro as fallback
```

---

### 3. pmdarima ⚠️ C COMPILER REQUIRED
**Status:** Not installed (compilation failed)  
**Impact:** ARIMA time series modeling  
**Solution:** Install Visual Studio Build Tools OR use statsmodels  
**Difficulty:** ⭐⭐⭐ (15-30 minutes for VS Build Tools)

#### Problem:
- Requires C compiler for Cython extensions
- Build fails with: `C1083: Cannot open source file: 'pmdarima/arima/_arima.c'`
- Missing: Visual Studio Build Tools with C++ support

#### Solutions:

**Option A: Install Visual Studio Build Tools (RECOMMENDED for pmdarima)**

1. **Download Build Tools:**
   - URL: https://visualstudio.microsoft.com/downloads/#build-tools-for-visual-studio-2022
   - File: vs_BuildTools.exe (~3.5 MB installer)

2. **Run Installer:**
   ```powershell
   # Download first
   Invoke-WebRequest -Uri "https://aka.ms/vs/17/release/vs_buildtools.exe" -OutFile "$env:TEMP\vs_buildtools.exe"
   
   # Run installer (GUI will open)
   Start-Process "$env:TEMP\vs_buildtools.exe"
   ```

3. **Select Workloads:**
   - ✅ Check: **"Desktop development with C++"**
   - Components auto-selected:
     - MSVC v143 - VS 2022 C++ x64/x86 build tools
     - Windows 11 SDK
     - C++ core features
   - Disk space: ~6.5 GB
   - Time: 15-30 minutes

4. **Install pmdarima:**
   ```powershell
   # After Build Tools installed, restart terminal
   pip install pmdarima
   ```

5. **Verify:**
   ```powershell
   python -c "import pmdarima; print('pmdarima version:', pmdarima.__version__)"
   ```

**Option B: Use statsmodels ARIMA (NO BUILD TOOLS NEEDED)**
```powershell
# statsmodels already installed, no additional packages needed
pip install statsmodels  # Already have this
```

```python
# In code, use statsmodels instead of pmdarima
from statsmodels.tsa.arima.model import ARIMA

# pmdarima auto_arima equivalent:
from statsmodels.tsa.stattools import arma_order_select_ic
```

**Option C: Pre-built Wheels (if available)**
```powershell
# Check if pre-built wheel exists for Python 3.13
pip install pmdarima --only-binary :all:
```

---

## Quick Fix Script

### Get to 11/13 (84.6%) - Easy Route

**Install PyKalman only:**
```powershell
pip install pykalman
```

**Result:** 11/13 libraries (84.6%)  
**Time:** 2 minutes  
**Risk:** None

---

### Get to 12/13 (92.3%) - Medium Route

**Install PyKalman + pmdarima with Build Tools:**

1. Install Visual Studio Build Tools (see Option A above)
2. Install libraries:
   ```powershell
   pip install pykalman
   pip install pmdarima
   ```

**Result:** 12/13 libraries (92.3%)  
**Time:** 30-45 minutes  
**Risk:** Low (large download, disk space)

---

### Get to 13/13 (100%) - Advanced Route

**Requires Python 3.12 downgrade:**

1. Install Python 3.12.x
2. Create new venv
3. Install all packages including PyMC/pytensor

**Result:** 13/13 libraries (100%)  
**Time:** 1-2 hours  
**Risk:** Medium (environment migration)

---

## Automated Installation Script

Create `install_missing_libs.ps1`:

```powershell
#!/usr/bin/env pwsh
# LOGOS Missing Libraries Installer

Write-Host "=== LOGOS Library Installer ===" -ForegroundColor Cyan
Write-Host ""

# Check Python version
$pyVersion = python --version
Write-Host "Python Version: $pyVersion" -ForegroundColor Yellow

# Option 1: PyKalman (Easy)
Write-Host "`n[1/3] Installing PyKalman..." -ForegroundColor Green
pip install pykalman
if ($LASTEXITCODE -eq 0) {
    Write-Host "  ✅ PyKalman installed successfully" -ForegroundColor Green
} else {
    Write-Host "  ❌ PyKalman installation failed" -ForegroundColor Red
}

# Option 2: pmdarima (Requires Build Tools)
Write-Host "`n[2/3] Checking for C++ compiler..." -ForegroundColor Green
$vsPath = "C:\Program Files (x86)\Microsoft Visual Studio\2022\BuildTools\VC\Tools\MSVC"
if (Test-Path $vsPath) {
    Write-Host "  ✅ Visual Studio Build Tools found" -ForegroundColor Green
    Write-Host "  Installing pmdarima..." -ForegroundColor Yellow
    pip install pmdarima
    if ($LASTEXITCODE -eq 0) {
        Write-Host "  ✅ pmdarima installed successfully" -ForegroundColor Green
    } else {
        Write-Host "  ❌ pmdarima installation failed" -ForegroundColor Red
    }
} else {
    Write-Host "  ⚠️  Visual Studio Build Tools not found" -ForegroundColor Yellow
    Write-Host "  Download from: https://visualstudio.microsoft.com/downloads/#build-tools-for-visual-studio-2022" -ForegroundColor Cyan
    Write-Host "  Select: 'Desktop development with C++'" -ForegroundColor Cyan
    Write-Host "  Skipping pmdarima..." -ForegroundColor Yellow
}

# Option 3: PyMC (Skip if Python 3.13)
Write-Host "`n[3/3] Checking PyMC compatibility..." -ForegroundColor Green
if ($pyVersion -match "3\.13") {
    Write-Host "  ⚠️  Python 3.13 detected - PyMC requires Python 3.10-3.12" -ForegroundColor Yellow
    Write-Host "  Skipping PyMC (use Pyro as alternative)" -ForegroundColor Yellow
} else {
    Write-Host "  Installing PyMC + pytensor..." -ForegroundColor Yellow
    pip install pymc
    if ($LASTEXITCODE -eq 0) {
        Write-Host "  ✅ PyMC installed successfully" -ForegroundColor Green
    } else {
        Write-Host "  ❌ PyMC installation failed" -ForegroundColor Red
    }
}

# Final status check
Write-Host "`n=== Final Library Status ===" -ForegroundColor Cyan
python check_libraries.py

Write-Host "`n=== Installation Complete ===" -ForegroundColor Cyan
Write-Host "Restart your terminal and test with: python gui.py" -ForegroundColor Yellow
```

---

## Testing After Installation

**Test PyKalman:**
```python
from pykalman import KalmanFilter
import numpy as np

kf = KalmanFilter(n_dim_obs=1, n_dim_state=1)
measurements = np.random.randn(100)
state_means, _ = kf.filter(measurements)
print("PyKalman working:", len(state_means) == 100)
```

**Test pmdarima:**
```python
from pmdarima import auto_arima
import numpy as np

data = np.random.randn(100)
model = auto_arima(data, seasonal=False, trace=False)
print("pmdarima working:", model is not None)
```

**Test PyMC (if Python 3.12):**
```python
import pymc as pm
import numpy as np

with pm.Model() as model:
    mu = pm.Normal('mu', mu=0, sigma=1)
    obs = pm.Normal('obs', mu=mu, sigma=1, observed=np.random.randn(100))
print("PyMC working: Model created")
```

---

## Recommended Action Plan

### For Most Users (Easy Path):

1. **Install PyKalman** (2 minutes)
   ```powershell
   pip install pykalman
   ```
   Result: **11/13 libraries (84.6%)**

2. **Test GUI:**
   ```powershell
   cd logos_alignment_core
   python gui.py
   ```

3. **Document limitations:**
   - PyMC: Requires Python 3.10-3.12 (use Pyro instead)
   - pmdarima: Requires Visual Studio Build Tools (use statsmodels instead)

### For Power Users (Advanced Path):

1. **Install Visual Studio Build Tools** (30 minutes)
   - Download and install "Desktop development with C++"
   
2. **Install all missing libraries:**
   ```powershell
   pip install pykalman pmdarima
   ```
   Result: **12/13 libraries (92.3%)**

3. **For 13/13:** Create Python 3.12 virtual environment

---

## Alternative Solutions

### gTTS as pyttsx3 Fallback
If pyttsx3 has issues on Windows:
```powershell
pip install gTTS
```

```python
# In gui.py, modify tts_output:
try:
    from gtts import gTTS
    import os
    
    def tts_fallback(text):
        tts = gTTS(text=text, lang='en')
        tts.save('temp_audio.mp3')
        os.system('start temp_audio.mp3')  # Windows
except ImportError:
    pass  # Silent fallback
```

### statsmodels ARIMA as pmdarima Fallback
Already installed, just use:
```python
from statsmodels.tsa.arima.model import ARIMA

# Instead of pmdarima.auto_arima:
model = ARIMA(data, order=(1,1,1))
result = model.fit()
```

---

## Summary Table

| Library | Status | Fix Difficulty | Time | Result |
|---------|--------|---------------|------|--------|
| **PyKalman** | ❌ Missing | ⭐ Easy | 2 min | 11/13 (84.6%) |
| **pmdarima** | ❌ Missing | ⭐⭐⭐ Medium | 30 min | 12/13 (92.3%) |
| **PyMC** | ⚠️ Installed but broken | ⭐⭐⭐⭐ Hard | 1-2 hrs | 13/13 (100%) |

**Recommended:** Install PyKalman only → 11/13 (84.6%)  
**Optional:** Add pmdarima with VS Build Tools → 12/13 (92.3%)  
**Advanced:** Python 3.12 venv for PyMC → 13/13 (100%)

---

## Next Steps

1. Run: `pip install pykalman`
2. Test: `python check_libraries.py`
3. Verify: `python gui.py`
4. Document final library count in GUI or README

---

**Guide Created:** October 25, 2025  
**Current Libraries:** 10/13 (76.9%)  
**Target:** 11/13 (84.6%) - Achievable in 5 minutes!
