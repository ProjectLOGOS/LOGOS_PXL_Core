# ChronoPraxis Constructive Core - Build System

## Overview

This document describes the build system for the ChronoPraxis constructive temporal logic framework. The system provides one-shot builds, tests, and CI hooks for the complete constructive proof system.

## Build System Components

### 1. PowerShell Build Script (`build.ps1`)

**Primary build tool** - Works reliably on Windows with Coq installed.

#### Usage:
```powershell
# Build all modules
.\build.ps1

# Clean build artifacts  
.\build.ps1 -Clean
```

#### Features:
- ✅ Builds modules in correct dependency order
- ✅ Clear progress indication
- ✅ Error handling with proper exit codes
- ✅ Includes smoke tests compilation
- ✅ Clean operation removes all build artifacts

### 2. VS Code Integration

#### Tasks Available:
- **Ctrl+Shift+P** → "Tasks: Run Task" → "coq: build all"
- **Ctrl+Shift+P** → "Tasks: Run Task" → "coq: clean" 
- **Ctrl+Shift+P** → "Tasks: Run Task" → "coq: test"

#### Build Keyboard Shortcut:
- **Ctrl+Shift+B** triggers the default build task

### 3. Traditional Makefile (Alternative)

For Unix-like environments or systems with proper Make:
```bash
make all    # Build all modules
make clean  # Clean artifacts  
make test   # Run smoke tests
```

## Module Structure

### Build Order (Dependency Graph):
```
ChronoAxioms.v
    ↓
Bijection.v
    ↓
ChronoMappings.v (requires ChronoAxioms + Bijection)
    ↓
ChronoTactics.v (requires ChronoAxioms + Bijection + ChronoMappings)
    ↓  
ChronoProofs.v (requires all above)
    ↓
ChronoPraxis.v (requires all above)
    ↓
SmokeTests.v (requires all above)
```

### Module Purposes:
- **ChronoAxioms.v**: Foundational temporal logic axioms
- **Bijection.v**: Constructive bijection interface with composition
- **ChronoMappings.v**: Bijective mappings between temporal modes
- **ChronoTactics.v**: Tactical support (normalize_time, specialized lemmas)
- **ChronoProofs.v**: Core constructive theorems + legacy proofs
- **ChronoPraxis.v**: Main interface module
- **SmokeTests.v**: Verification of constructive properties

## Constructive Core Theorems

The build system ensures these core theorems are constructively proven:

### 1. **temporal_convergence**
```coq
Theorem temporal_convergence :
  forall pA : PA, ChronoMappings.C_to_A (ChronoMappings.A_to_C pA) = pA.
```

### 2. **chronological_collapse** (A, B, C variants)
```coq
Theorem chronological_collapse_A : 
  forall pA:PA, (ChronoMappings.B_to_A (ChronoMappings.A_to_B pA)) = pA.
```

### 3. **causal_bijection** (forward + backward)
```coq
Theorem causal_bijection_forward :
  forall pA, ChronoMappings.C_to_A (ChronoMappings.A_to_C pA) = pA.
```

### 4. **temporal_consistency**
```coq
Theorem temporal_consistency :
  forall pA : PA, 
    ChronoMappings.A_to_C pA = (ChronoMappings.B_to_C (ChronoMappings.A_to_B pA)) /\ 
    ChronoMappings.A_to_C pA = (ChronoMappings.A_to_C pA).
```

## Testing Framework

### Smoke Tests (`SmokeTests.v`)
- **Basic bijection properties**: Tests all A↔B, B↔C round trips
- **Constructive theorem availability**: Verifies core theorems are accessible
- **Type safety**: Ensures proper PA → PB → PC type flow

### Test Execution
```powershell
# Run via build script (includes tests)
.\build.ps1

# Or via VS Code task
# Ctrl+Shift+P → "Tasks: Run Task" → "coq: test"
```

## CI/CD Integration

### GitHub Actions Ready
The build system is designed for easy CI integration:

```yaml
# Example GitHub Actions step
- name: Build ChronoPraxis
  run: |
    powershell -ExecutionPolicy Bypass -File ./build.ps1
```

### Requirements:
- **Coq 8.15+** (tested with 8.18)
- **PowerShell** (Windows) or **Make** (Unix-like)
- **coqc** in PATH

## Success Indicators

### Build Success:
```
✅ ChronoPraxis constructive core is ready.
```

### All Tests Pass:
```
✅ Smoke tests passed - all constructive theorems verified.
```

## Troubleshooting

### Common Issues:

1. **"coqc not found"**
   - Ensure Coq is installed and `coqc` is in PATH
   
2. **Module import warnings**
   - These are harmless deprecation warnings (masking-absolute-name)
   - All modules compile successfully despite warnings

3. **PowerShell execution policy**
   - Run: `Set-ExecutionPolicy -ExecutionPolicy RemoteSigned -Scope CurrentUser`
   - Or use the VS Code tasks which bypass the policy

### Build from Scratch:
```powershell
# Clean everything and rebuild
.\build.ps1 -Clean
.\build.ps1
```

## Architecture Notes

- **Constructive Foundation**: No classical axioms, no admits in core theorems
- **Pure Bijection Properties**: All proofs use explicit `fg` and `gf` fields
- **Windows-First**: Primary development and testing on Windows with PowerShell
- **Cross-Platform**: Makefile provided for Unix-like systems