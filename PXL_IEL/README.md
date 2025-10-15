# PXL_IEL (PXL Kernel + IEL Overlays)
- `pxl/` : PXL kernels & provers
- `iels/`: IEL overlays (e.g., ArithmoPraxis) + their Coq code
- `proofs/`: Coq proofs, tests, extraction
- `docs/`: specs & build notes
Build: `coq_makefile -f _CoqProject -o Makefile && make -j2`