# Verified Slice Manifest
# LOGOS PXL Core - Mathematically Verified Components

## Verification Status
- **Verification Tool**: coqchk 8.20.1
- **Verification Date**: $(Get-Date -Format "yyyy-MM-dd")
- **Verification Result**: All modules pass formal verification

## Verified Components
### PXLs.PXLv3
- **Location**: pxl-minimal-kernel-main/coq/PXLv3.v
- **Verification**: ✓ coqchk verified
- **Content**: Core modal logic kernel (S5 axioms, natural deduction)
- **Extracted**: pxl_core.ml (syntactic types)

### PXLs.IEL.Source.TheoPraxis.Props
- **Location**: modules/IEL/source/TheoPraxis/Props.v
- **Verification**: ✓ coqchk verified
- **Content**: Philosophical property classes and instances
- **Extracted**: pxl_core.ml (property types)

## Quarantined Components (Experimental)
- ChronoPraxis.Core
- ChronoAxioms.v
- ChronoMappings.v
- All modules with Axiom/Parameter/Admitted

## Runtime Artifacts
- **OCaml Extraction**: pxl_core.ml, pxl_core.mli
- **Container**: Dockerfile.pxl-core
- **Verification**: SHA256 checksums included

## Security Properties
- **Formal Verification**: All runtime code derived from proven theorems
- **Contamination Check**: No experimental dependencies
- **Provenance**: Git tag v3.0.0-verified
- **CI Guards**: Automated verification in .github/workflows/

## Deployment
- **Container Registry**: Ready for deployment behind gateway
- **Health Checks**: Built-in runtime verification
- **SBOM**: SPDX format available