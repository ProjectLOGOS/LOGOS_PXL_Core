# Contributing to LOGOS_PXL_Core

## Toolchain
- Coq: **8.20.1** (or Coq Platform 2024.09)
- Coq SerAPI: **0.19.0+coq8.20**
- OCaml: as bundled with Coq Platform
- Python: 3.10+
- Docker (optional): 24+

## Quick Start
```bash
git clone https://github.com/ProjectLOGOS/LOGOS_PXL_Core.git
cd LOGOS_PXL_Core
# Verify kernel (build + coqchk + deterministic hash)
ci/verify_pxl.sh
# Build everything and run smoke tests
make coq-all
make coq-test
```

## Development Workflow

* Branch from `main`, name: `feat/<short>`, `fix/<short>`, or `docs/<short>`.
* Add tests under `tests/` or IEL-specific test dirs.
* Run `ci/verify_pxl.sh` before pushing. PRs must pass `coqchk` and hash pin check.

## Code Standards

* Coq files: keep imports explicit and stable; prefer `Require Import` over `Load`.
* No new axioms in kernel; overlays must declare classical assumptions clearly.
* Python: `ruff` and `pytest` where applicable.

## PR Checklist

* [ ] `ci/verify_pxl.sh` passes locally
* [ ] `make coq-all && make coq-test` succeeds
* [ ] Docs updated (COQ index and relevant README)
* [ ] Minimal, focused diffs