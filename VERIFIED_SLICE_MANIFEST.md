# Verified Slice Manifest
# LOGOS PXL Core - Mathematically Verified Components

## Verification Status
- **Verification Tool**: coqchk 8.20.1
- **Verification Date**: 2025-10-10
- **Verification Result**: All modules pass formal verification
- **Build SHA**: 40360dc
- **Release Tag**: v3.0.0-verified

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
- **Runtime Server**: pxl_runtime.ml
- **Build System**: dune-project
- **Container**: Dockerfile.pxl-core
- **Orchestration**: docker-compose.verified.yml
- **Load Testing**: k6/verified-core-baseline.js

## Security Properties
- **Formal Verification**: All runtime code derived from proven theorems
- **Contamination Check**: No experimental dependencies
- **Provenance**: Git tag v3.0.0-verified, SHA 40360dc
- **CI Guards**: Automated verification in .github/workflows/
- **Container Security**: Non-root user, read-only filesystem, dropped capabilities

## Deployment
- **Container Registry**: Ready for deployment behind gateway
- **Health Checks**: HTTP endpoints at /health and /proof/ping
- **Provenance Headers**: X-PXL-Coqchk, X-Build-SHA, X-Release-Tag
- **Load Baseline**: k6 tests for performance monitoring
- **SBOM**: SPDX format available

## API Endpoints
- `GET /health` - Health check with verification metadata
- `GET /proof/ping` - Proof that verified core is loaded

## Production Checklist
- [x] Formal verification complete
- [x] Contamination quarantine enforced
- [x] OCaml extraction successful
- [x] Container build configured
- [x] Health checks implemented
- [x] Load testing baseline created
- [x] Security hardening applied
- [x] CI/CD gates active
- [ ] Container build tested
- [ ] Load testing executed
- [ ] Production deployment complete