# PXL Final Proofs

This repository contains the final proofs for the Protopraxic Logic (PXL) system, a modal logic framework.

## Core Phases

- **Phase 1**: Inductive syntax and Prov relation (`PXLv3.v`)
- **Phase 2**: Meta-theorems (`PXLv3_Meta.v`)
- **Phase 3**: S5 Kripke semantics (`S5_Kripke.v`)
- **Phase 5**: Decidability (`PXL_Decidability.v`)

## Triune Overlay

The triune overlay provides theology-neutral proofs of triune grounding formulas using PXL semantics.

### Goals
- Prove necessary co-existence, unity, distinction, and grounded laws of thought.
- Maintain absolute neutrality: no theological axioms in the core.
- Non-intrusion guarantee: overlay can be removed without affecting core proofs.

### Building
```bash
make  # Builds core
coqchk -quiet -R coq PXLs  # Verifies core
```

### Enabling Overlay
To include the triune overlay:
```bash
# The overlay is included in the main build
make
coqchk -quiet -R coq PXLs
```

### Files
- `PXL_TriuneTheory.v`: Definitions and theorem statements.
- `PXL_Completeness_Interface.v`: Thin interface for proofs.
- `PXL_Completeness_Instance.v`: Concrete completeness instance.

### Hygiene
Zero `Axiom`/`Admitted`/`Parameter` in core; overlay has placeholders for proofs.

### Disabling Overlay
Remove `PXL_TriuneTheory.v`, `PXL_Completeness_Interface.v`, `PXL_Completeness_Instance.v` from `_CoqProject` and rebuild.
# PXL Total Packet

- Core phases (15): constructive, self-contained, kernel-verified.
- Phase 4: completeness via localized canonical lemmas (scoped to Phase-4; core hygiene intact).
- Overlays (Triune Theory / Metaphysical Necessity): separate, removable, with admits where they encode extra-logical theses.
- Build: Coq 8.20.1, OCaml 4.14.2.

## Build & Verify
1. Clone: `git clone https://github.com/ProjectLOGOS/pxl-minimal-kernel.git`
2. Open PowerShell in this folder.
3. Run: .\verify.ps1
   - Compiles with coqc (Prelude via -R "C:\Coq-Platform~8.20~2025.01\lib\coq\theories" Coq and logical path -Q coq PXLs)
   - Runs coqchk
   - Runs hygiene scan (Axiom|Admitted|Parameter) and saves hygiene.txt

## Hygiene Policy
- Core files: no Axiom/Parameter; admits only where documented (e.g., decidability/completeness internals if present in your snapshot).
- Overlays: admits may remain for metaphysical statements; they are removable without affecting core.


### Toolchain install (Coq Platform)
Install Coq Platform 2024.09 (Coq 8.20.1). On Ubuntu CI we use `coqorg/coq:8.20.1`.
