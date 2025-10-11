# LOGOS V3 Integration Guide

This guide covers the process of scanning, importing, and integrating V3 modules from `C:\Users\proje\OneDrive\Desktop\LOGOS SYSTEM\v3` into the LOGOS PXL Core repository.

## Prerequisites

- PowerShell 5.1+ with `Select-String` support
- VS Code with Coq extension
- Access to `C:\Users\proje\OneDrive\Desktop\LOGOS SYSTEM\v3`

## Step 1: Scan V3 Directory for Target Modules

Run the scan to find relevant modules containing:
- Gödelian Desire Driver
- Trinitarian Axiom of Choice
- Causal simulator components
- Recursive goal engines
- Planners and workflows
- Hyper-nodes

### Option A: Run PowerShell Script Directly
```powershell
.\scan_v3_modules.ps1
```

### Option B: Use VS Code Task
- Ctrl+Shift+P → "Tasks: Run Task"
- Select "Scan V3 for targets"

### Option C: Manual VS Code Search
- Ctrl+Shift+F (global search)
- Enable regex (.*)
- Query: `G(ö|o)delian.*Desire.*Driver|Trinitarian.*Axiom.*Choice|causal.*simulat|recursive.*goal|goal\s*engine|planner|workflow|hyper[\- ]node`

Results will be saved to `reports/v3_scan_hits.tsv`.

## Step 2: Mirror V3 Code to Vendor Directory

```powershell
.\mirror_v3_code.ps1
```

This creates `third_party/logos_agi_v4_local/` with a clean copy of V3 code, excluding build artifacts.

## Step 3: Generate Coq Load Paths

```powershell
.\generate_coq_paths.ps1
```

This outputs the `-Q` entries to add to `_CoqProject`. Copy these lines into your `_CoqProject` file.

## Step 4: Update V4 Adapters

Based on the scan results, update the adapter files in `coq/V4Adapters/`:

### Knowledge.v
- Maps V4 epistemic types to IEL GnosiPraxis
- Update `Require Import` statements to point to discovered modules

### Action.v
- Maps V4 action types to IEL ErgoPraxis
- Update for decision theory and Hoare logic components

### Value.v
- Maps V4 value types to IEL Axiopraxis
- Update for utility theory and preference components

## Step 5: Create Shim Modules (if needed)

If file names or module structures differ, create shims in `coq/V4Adapters/Shims/`:

```coq
(* Example shim for renamed module *)
From V4.Vendor.Path Require Import OldName.
Module NewName := OldName.
```

## Step 6: Validate Integration

```powershell
.\validate_v3_import.ps1
```

This runs:
- Full Coq build
- coqchk verification on verified slice
- Axiom/Admitted scan in vendor code

## Expected Scan Results

Look for hits containing:

### Gödelian Desire Driver
- Candidate recursive goal engine
- May contain self-referential goal structures

### Trinitarian Axiom of Choice
- **SECURITY NOTE**: If this is an axiom (not constructively proven), quarantine or re-express before integration
- May require formal verification cleanup

### Causal Simulator Components
- Look for: "do-calculus", "Pearl", "intervention", "SCM" (Structural Causal Model)
- These provide causal reasoning capabilities

## Integration Checklist

- [ ] V3 directory scanned
- [ ] Relevant modules identified in `reports/v3_scan_hits.tsv`
- [ ] Code mirrored to `third_party/logos_agi_v4_local/`
- [ ] Coq load paths added to `_CoqProject`
- [ ] Adapter files updated with correct `Require Import` statements
- [ ] Shim modules created for name mismatches
- [ ] Build validation passes
- [ ] No Axiom/Admitted in verified slice
- [ ] Coqchk verification succeeds

## Next Steps

After successful integration:
1. Convert vendor directory to Git submodule (when V3 becomes a remote repo)
2. Expand verified slice to include V3 components
3. Add formal guards for Themi/Gnosi/Ergo overlays
4. Schedule quarterly proof debt reviews