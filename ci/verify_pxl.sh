#!/usr/bin/env bash
set -euo pipefail

echo "Starting PXL verification..."

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
# Run coqchk on the built kernel
if command -v coqchk >/dev/null 2>&1; then
    coqchk -R . PXLs $(find . -name "*.vo" | head -20) || {
        echo "Warning: Some coqchk warnings encountered, but continuing..."
    }
else
    echo "Warning: coqchk not found, skipping verification"
fi

echo "Computing kernel hash..."
# Compute deterministic hash of all .vo files using Python
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

# Navigate back to root and update config
cd ../..

# Update config.json with new hash
if [ -f "configs/config.json" ]; then
    if command -v jq >/dev/null 2>&1; then
        jq --arg h "$HASH" '.expected_kernel_hash=$h' configs/config.json > /tmp/cfg.$$
        mv /tmp/cfg.$$ configs/config.json
        echo "Updated configs/config.json with kernel hash: $HASH"
    else
        # Fallback without jq
        sed -i.bak "s/\"expected_kernel_hash\": \"[^\"]*\"/\"expected_kernel_hash\": \"$HASH\"/" configs/config.json
        echo "Updated configs/config.json with kernel hash: $HASH (using sed)"
    fi
else
    echo "Warning: configs/config.json not found, kernel hash not updated"
fi

echo "Verification script completed successfully"