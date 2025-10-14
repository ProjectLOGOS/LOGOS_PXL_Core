# IEL–MathPraxis (LOGOS)

MathPraxis turns LOGOS/PXL modal claims into **constructive, auditable artifacts**.

**Pipeline:** Spec (PXL/Modal) → Witness/Verifier (constructive) → Scan/Logs (evidence)

## Structure

```
modules/iel-math/MathPraxis/
├── Core/
│   ├── ModalWrap.v          # Modal logic operators (□/◇) for PXL integration
│   └── Numbers.v            # Number theory foundations and primality
├── Problems/
│   └── Goldbach/
│       ├── Spec.v          # Classical + modal forms with bridge axioms
│       ├── Extract.v       # Witness finder for prime pairs
│       ├── Verify.v        # Verification of witness correctness
│       └── Scan.v          # vm_compute testing + CSV logging
├── Meta/
│   └── Realizability.v     # Bridge between modal logic and programs
├── scripts/                 # Build and extraction scripts
└── logs/                   # Computational evidence logs
```

## Current Status - Goldbach v0.1

- ✅ **Spec.v**: Classical + modal forms with bridge hooks
- ✅ **Extract.v**: Naive witness finder (upgradable to certified)
- ✅ **Verify.v**: Small-range soundness lemma (to be completed)
- ✅ **Scan.v**: vm_compute sanity + CSV-ready log lines
- ✅ **Modal Integration**: Prepared for PXL framework connection

## Quick Test

```coq
From MathPraxis.Problems.Goldbach Require Import Scan.
Eval vm_compute in (GoldbachScan.count_ok 2 10).
```

This counts satisfied even numbers in a small range, demonstrating the constructive approach.

## Build Instructions

1. Ensure `_CoqProject` includes the MathPraxis mapping
2. Generate Makefile: `coq_makefile -f _CoqProject -o Makefile`
3. Compile: `make -j4`
4. Test in Coq with the import above

## Next Steps

- **Certified Primality**: Replace naive `is_prime` with Pocklington or Miller-Rabin + proofs
- **Large-N Scans**: Optimize for computational verification at scale
- **Realizability Lemmas**: Complete the □/◇ ⇒ programs bridge
- **PXL Integration**: Connect modal operators to verified PXL framework
- **Extraction**: Generate OCaml/Haskell code for large-scale verification

## Philosophy

**IEL-MathPraxis** demonstrates that LOGOS can bridge **pure mathematics** and **constructive verification**:

1. **Modal Specifications**: Express mathematical conjectures using LOGOS modal logic
2. **Constructive Witnesses**: Generate computational evidence through Coq programs
3. **Formal Bridges**: Prove that modal statements imply classical theorems
4. **Auditable Evidence**: Produce verifiable computational logs

This creates a new paradigm where mathematical claims are backed by **constructive proof + computational verification**, making LOGOS uniquely suited for trustworthy mathematical AI.
