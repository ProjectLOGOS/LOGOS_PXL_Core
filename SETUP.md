# LOGOS AGI - Setup & Installation Guide

**Version:** Phase 1 Complete  
**Date:** October 25, 2025  
**Python Version:** 3.13 (with compatibility notes)

---

## 📋 System Requirements

### Core Requirements
- **Python:** 3.11, 3.12, or 3.13
- **pip:** 25.3 or higher
- **OS:** Windows 10/11, Linux, macOS
- **Memory:** 8GB RAM minimum (16GB recommended for ML operations)
- **Disk Space:** 5GB for dependencies and models

### Optional Requirements
- **C/C++ Compiler:** Required for pmdarima (MSVC on Windows, gcc/clang on Linux/macOS)
- **CUDA:** Optional for PyTorch GPU acceleration
- **Microphone:** Optional for voice input features

---

## 🚀 Quick Start Installation

### Step 1: Clone Repository
```powershell
git clone https://github.com/ProjectLOGOS/LOGOS_PXL_Core.git
cd LOGOS_PXL_Core
```

### Step 2: Install Core Dependencies
```powershell
pip install --upgrade pip setuptools wheel
pip install -r requirements.txt
```

### Step 3: Verify Installation
```powershell
python phase1_status.py
```

Expected output: **11/13 libraries loaded** (84.6% success rate)

---

## 📦 Library Installation Status

### ✅ Verified Working (11 libraries)

| Library | Version | Purpose | Python 3.13 |
|---------|---------|---------|-------------|
| Pyro | 1.8.6 | Probabilistic programming | ✅ Compatible |
| PyTorch | 2.3.0 | Deep learning framework | ✅ Compatible |
| Sentence Transformers | 2.7.0 | NLP embeddings (384-dim) | ✅ Compatible |
| NetworkX | 3.3 | Graph analysis | ✅ Compatible |
| Arch | 8.0.0 | Econometric modeling (GARCH) | ✅ Compatible |
| FilterPy | 1.4.5 | Kalman filtering (primary) | ✅ Compatible |
| PyKalman | 0.9.5 | Kalman filtering (backup) | ✅ Compatible |
| Scikit-learn | 1.5.0 | ML algorithms | ✅ Compatible |
| Tkinter | Built-in | GUI framework | ✅ Compatible |
| Speech Recognition | Optional | Voice input | ⚠️ Not installed |
| pyttsx3 | Optional | Text-to-speech | ⚠️ Not installed |

### ❌ Incompatible with Python 3.13 (2 libraries)

| Library | Reason | Workaround |
|---------|--------|------------|
| PyMC | Requires pytensor 2.18.1-2.19 (unavailable for Py 3.13) | Use Python 3.11/3.12 |
| pmdarima | Cython build fails, requires C compiler | Use Python 3.11/3.12 with MSVC |

---

## 🔧 Python Version Compatibility

### Recommended: Python 3.11 or 3.12
For **full 13/13 library support**, use Python 3.11 or 3.12:

```powershell
# Install Python 3.12
pyenv install 3.12.0
pyenv local 3.12.0

# Install all libraries
pip install -r requirements.txt
pip install pymc==5.10.4 pmdarima==2.0.4
```

### Current: Python 3.13
- ✅ **11/13 libraries working** (84.6%)
- ❌ PyMC unavailable (probabilistic programming)
- ❌ pmdarima unavailable (auto-ARIMA)
- ✅ System fully functional with graceful degradation

---

## 🛠️ Troubleshooting

### Issue: "No module named 'pymc'"
**Cause:** PyMC requires pytensor 2.18.1-2.19, which doesn't support Python 3.13  
**Solution:** Either:
1. Use Python 3.11/3.12
2. Continue without PyMC (Pyro provides similar probabilistic programming)

### Issue: "Failed building wheel for pmdarima"
**Cause:** pmdarima requires C compiler for Cython extensions  
**Solution:** Either:
1. Install Microsoft Visual C++ Build Tools:
   ```powershell
   # Download from: https://visualstudio.microsoft.com/downloads/
   # Select "Desktop development with C++" workload
   ```
2. Use Python 3.11/3.12 with pre-built wheels
3. Continue without pmdarima (other time series methods available)

### Issue: "Defaulting to user installation"
**Cause:** System-wide site-packages not writable  
**Solution:** This is normal and safe. Packages install to user directory.

### Issue: FilterPy/Arch not loading
**Cause:** May have installed to wrong location  
**Solution:**
```powershell
pip install --user arch==8.0.0 filterpy==1.4.5
python phase1_status.py  # Verify
```

---

## 🧪 Testing Installation

### Basic Test
```powershell
python phase1_status.py
```

### Comprehensive Test
```powershell
python demo_extensions.py
```

### Run Test Suite
```powershell
pytest tests/test_extensions.py -v
```

### Test Individual Libraries
```python
from boot.extensions_loader import extensions_manager

# Initialize
extensions_manager.initialize()

# Test NetworkX
graph = extensions_manager.build_graph(['A', 'B'], [('A', 'B')])
print(extensions_manager.analyze_graph(graph))

# Test Sentence Embeddings
embedding = extensions_manager.embed_sentence("Test sentence")
print(f"Embedding dims: {len(embedding)}")

# Test Kalman Filter
filtered = extensions_manager.kalman_filter([1.0, 1.1, 0.9])
print(f"Filtered: {filtered}")
```

---

## 📊 Performance Expectations

### Boot Time
- **Cold start:** 2-3 seconds (loading 11 libraries)
- **Warm start:** <1 second (cached imports)

### Memory Usage
- **Base system:** ~200MB
- **With PyTorch + Transformers:** ~700MB
- **Peak (sentence embeddings):** ~1.2GB

### Model Downloads (First Run Only)
- Sentence Transformers (all-MiniLM-L6-v2): ~90MB
- One-time download, cached locally

---

## 🔒 Security & Proof-Gating

### PXL Integration
All libraries are proof-gated with obligations:
- `BOX(SafeProbabilisticModel())` - Pyro, PyMC
- `BOX(SafeTensorOps())` - PyTorch
- `BOX(SafeNLPTransform())` - Sentence Transformers
- `BOX(SafeGraphOps())` - NetworkX
- `BOX(SafeEconometricModel())` - Arch
- `BOX(SafeFilterOps())` - FilterPy, PyKalman
- `BOX(SafeMLModel())` - Scikit-learn
- `BOX(SafeUIThread())` - Tkinter

### Audit Logging
All library load attempts logged:
```python
audit_log = extensions_manager.get_audit_log()
# View decision history: 'allow' or 'deny'
```

### Fail-Closed Behavior
- Missing libraries → System continues with degraded functionality
- Failed proof validation → Library blocked, operation rejected
- Import errors → Gracefully handled, audit trail preserved

---

## 🌐 Optional Voice/GUI Features

### Voice Input (Optional)
```powershell
pip install SpeechRecognition==3.10.0 pyaudio==0.2.13
```

**Note:** PyAudio requires PortAudio library:
- **Windows:** Pre-built wheels usually work
- **Linux:** `sudo apt-get install portaudio19-dev`
- **macOS:** `brew install portaudio`

### Text-to-Speech (Optional)
```powershell
pip install pyttsx3==2.90
```

Works on all platforms with system TTS engines.

---

## 📁 Project Structure

```
LOGOS_PXL_Core/
├── boot/
│   ├── __init__.py
│   └── extensions_loader.py       # Main extensions manager (450+ lines)
├── tests/
│   └── test_extensions.py         # Test suite (350+ lines)
├── examples/
│   └── demo_integrated_ml.py      # ML/NLP integration demo
├── requirements.txt               # Dependency list with versions
├── phase1_status.py               # Quick status check
├── demo_extensions.py             # Interactive demo
├── SETUP.md                       # This file
└── PHASE_1_COMPLETION.md          # Detailed completion report
```

---

## 🔄 Upgrading Dependencies

### Safe Upgrade
```powershell
# Upgrade specific library
pip install --upgrade sentence-transformers

# Verify still works
python phase1_status.py
```

### Full Upgrade (Caution)
```powershell
# May break compatibility
pip install --upgrade -r requirements.txt
```

---

## 🐛 Reporting Issues

### Collect Diagnostic Info
```powershell
# Python version
python --version

# Installed packages
pip list > installed_packages.txt

# Library status
python phase1_status.py > status_report.txt

# Run tests
pytest tests/test_extensions.py -v > test_results.txt
```

### Submit Issue
Include:
1. Python version
2. Operating system
3. Status report (`status_report.txt`)
4. Error messages
5. Steps to reproduce

---

## ✅ Verification Checklist

- [ ] Python 3.11, 3.12, or 3.13 installed
- [ ] pip upgraded to 25.3+
- [ ] `requirements.txt` dependencies installed
- [ ] `python phase1_status.py` shows 11/13 libraries
- [ ] `python demo_extensions.py` runs without errors
- [ ] PyTorch operational (`pytorch_available()` returns True)
- [ ] Sentence embeddings working (384-dim vectors)
- [ ] NetworkX graphs constructing
- [ ] FilterPy Kalman filtering functional
- [ ] Scikit-learn classification working
- [ ] Audit log capturing all load attempts

---

## 📚 Next Steps

1. **Phase 1 Complete:** External library integration ✅
2. **Phase 2 Starting:** Trinity Knot GUI development
3. **Future:** Multi-modal reasoning, real-time visualization

---

## 🆘 Support

- **Documentation:** See `PHASE_1_COMPLETION.md`
- **Examples:** Run `examples/demo_integrated_ml.py`
- **Tests:** `pytest tests/test_extensions.py -v`
- **Issues:** GitHub Issues (ProjectLOGOS/LOGOS_PXL_Core)

---

*Last Updated: October 25, 2025*  
*LOGOS AGI Project - Phase 1 Complete*
