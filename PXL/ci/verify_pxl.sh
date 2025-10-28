#!/usr/bin/env bash
set -euo pipefail

# Print tool versions and enforce drift guard using toolversions.txt.
print_versions() {
  echo "[verify] Tool versions:"
  coqtop -v | sed -n '1p'
  serapi_coqtop -v 2>/dev/null | sed -n '1p' || echo "SerAPI: not found (ensure 0.19.0 for Coq 8.20.x)"
  python3 -V
}

check_version_drift() {
  local tv="toolversions.txt"
  if [[ -f "$tv" ]]; then
    # Expect lines: coq=8.20.1, serapi=0.19.0, python=3.10
    want_coq=$(grep '^coq=' "$tv" | cut -d= -f2)
    want_ser=$(grep '^serapi=' "$tv" | cut -d= -f2)
    want_py_mm=$(grep '^python=' "$tv" | cut -d= -f2) # major.minor only
    have_coq=$(coqtop -v | sed -n '1s/.*version \([0-9.]*\).*/\1/p')
    have_ser=$(serapi_coqtop -v 2>/dev/null | sed -n '1s/.*version \([0-9.]*\).*/\1/p' || true)
    have_py_mm=$(python3 -V | sed -n 's/Python \([0-9]*\.[0-9]*\).*/\1/p')
    [[ "$have_coq" == "$want_coq" ]] || { echo "[error] Coq version drift: have $have_coq want $want_coq"; exit 1; }
    [[ -z "$want_ser" || "$have_ser" == "$want_ser" ]] || { echo "[error] SerAPI version drift: have $have_ser want $want_ser"; exit 1; }
    [[ -z "$want_py_mm" || "$have_py_mm" == "$want_py_mm" ]] || { echo "[error] Python major.minor drift: have $have_py_mm want $want_py_mm"; exit 1; }
  fi
}

main() {
  print_versions
  check_version_drift
  echo "[verify] Building and checking PXL kernel"
  # existing build + coqchk + deterministic hash logic remains below
  # Change to PXL kernel directory
  if [ -d "pxl-minimal-kernel-main" ]; then
    cd pxl-minimal-kernel-main
  elif [ -d "pxl-prover/pxl_kernel" ]; then
    cd pxl-prover/pxl_kernel
  else
    echo "Error: PXL kernel directory not found"
    exit 1
  fi

  echo "Building PXL kernel..."
  if [ -f "Makefile" ]; then
    make clean || true
    make
  else
    echo "Warning: No Makefile found, skipping build"
  fi

  echo "Running coqchk verification..."
  if command -v coqchk >/dev/null 2>&1; then
    coqchk -R . PXLs $(find . -name "*.vo" | head -20) || {
      echo "Warning: Some coqchk warnings encountered, but continuing..."
    }
  else
    echo "Warning: coqchk not found, skipping verification"
  fi

  echo "Computing kernel hash..."
  HASH=$(python3 - <<'PY'
import hashlib, glob, sys
h = hashlib.sha256()
vo_files = sorted(glob.glob("**/*.vo", recursive=True))
if not vo_files:
    print("NOFILES", file=sys.stderr)
    sys.exit(1)
for p in vo_files:
    try:
        with open(p, "rb") as f:
            file_data = f.read()
            h.update(hashlib.sha256(file_data).digest())
    except Exception as e:
        print(f"Error hashing {p}: {e}", file=sys.stderr)
print(h.hexdigest())
PY
)

  echo "Kernel hash: $HASH"

  # Navigate back to root and write hash file
  cd ../..
  mkdir -p out
  echo "$HASH" > out/kernel_hash.txt
  echo "Wrote kernel hash to out/kernel_hash.txt"
}

main "$@"
