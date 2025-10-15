# ArithmoPraxis Infrastructure IEL

**ArithmoPraxis** is the infrastructure-level mathematical foundation for LOGOS/PXL modal reasoning systems. It provides constructive, auditable mathematical capabilities across all major mathematical domains.

## Purpose

ArithmoPraxis serves as the **mathematical substrate** for other IEL components, enabling:
- Modal mathematical reasoning with formal guarantees
- Constructive witness generation for mathematical claims
- Cross-domain mathematical verification and proof automation
- Infrastructure-level mathematical services for LOGOS AGI components

## Module Tree

```
IEL.ArithmoPraxis/
├── Core/                    # Foundation: modal logic + number theory
│   ├── ModalWrap.v         # □/◇ operators for PXL integration
│   └── Numbers.v           # Number theory substrate
├── Meta/                   # Infrastructure services
│   ├── Realizability.v    # Modal → constructive bridges
│   └── SIGNALS.v          # IEL interface contracts
├── Examples/              # Domain demonstrations
│   └── Goldbach/         # Conjecture verification + invariant mining
└── Mathematical Domains/ # Complete discipline scaffolds
    ├── BooleanLogic/     # SAT solving, decision procedures
    ├── ConstructiveSets/ # Choice-free set theory
    ├── CategoryTheory/   # Functors, topoi, higher categories
    ├── TypeTheory/       # HoTT, univalence, dependent types
    ├── NumberTheory/     # Cryptography, primes, modular arithmetic
    ├── Algebra/          # Groups, rings, Galois theory
    ├── Geometry/         # Euclidean, differential, algebraic
    ├── Topology/         # Metric spaces, algebraic topology
    ├── MeasureTheory/    # Integration, functional analysis
    ├── Probability/      # Stochastic processes, statistics
    └── Optimization/     # Linear programming, game theory
```

## How to Build

### Prerequisites
- Coq 8.15+
- Make
- Standard library dependencies

### Build Process
```bash
# Generate Makefile
coq_makefile -f _CoqProject -o Makefile

# Build all modules
make -j4

# Test core functionality
coqc tests/arithmo_suite.v

# Run benchmarks
./scripts/bench.sh
```

### Verification
```coq
From IEL.ArithmoPraxis.Examples.Goldbach Require Import ScanFeatures.
Eval vm_compute in (ScanFeatures.closure_score 100).
(* Expected: ~80-90 successful closures *)
```

## How Other IELs Call ArithmoPraxis

ArithmoPraxis exposes standardized interfaces through `Meta/SIGNALS.v`:

### Specification Requests
```coq
From IEL.ArithmoPraxis.Meta Require Import SIGNALS.

(* Request mathematical specification *)
Definition req := {| sr_name := "goldbach"; sr_formula := forall n, ... |}.
Definition ack := arithmo_spec req.
```

### Witness Generation
```coq
(* Request constructive witness *)
Definition wreq := {| wr_name := "goldbach"; wr_n := 20 |}.
Definition wack := arithmo_witness wreq.
(* Returns: {| wa_found := true; wa_p1p2 := Some (7,13) |} *)
```

### Proof Services
```coq
(* Request formal proof *)
Definition preq := {| pr_name := "lemma_x"; pr_goal := ... |}.
Definition pack := arithmo_proof preq.
```

## Integration Examples

### From Modal Reasoning IEL
```coq
From IEL.ModalReasoning Require Import Core.
From IEL.ArithmoPraxis.Meta Require Import SIGNALS.

(* Modal claim needs mathematical backing *)
Definition modal_math_query (φ : ModalFormula) : SpecAck :=
  arithmo_spec {| sr_name := "verify_modal"; sr_formula := interpret φ |}.
```

### From Planning IEL
```coq
From IEL.Planning Require Import Goals.
From IEL.ArithmoPraxis.Examples.Goldbach Require Import ScanFeatures.

(* Planning needs mathematical constraints *)
Definition constraint_check (n : nat) : bool :=
  match arithmo_witness {| wr_name := "goldbach"; wr_n := n |} with
  | {| wa_found := true |} => true
  | _ => false
  end.
```

## Performance Characteristics

- **Core Operations**: O(1) modal operations, O(√n) primality testing
- **Witness Generation**: Optimized for numbers up to 10^6
- **Closure Analysis**: 88% success rate on Goldbach invariants
- **Compilation**: ~30 seconds for full build on modern hardware

## Status & Roadmap

| Component | Status | Notes |
|-----------|--------|-------|
| **Core** | ✅ Complete | Modal logic + number theory substrate |
| **Goldbach Example** | ✅ Complete | Invariant mining, 88% closure rate |
| **IEL Interfaces** | ✅ v0.3 | SIGNALS protocol implemented |
| **CI/Testing** | ✅ v0.3 | GitHub Actions + test suite |
| **Realizability** | 🚧 Partial | First lemmas discharged |
| **Domain Expansion** | 🚧 Planned | Boolean logic → Set theory → Category theory |

### Next Phases
- **v0.4**: Complete Boolean logic and constructive sets domains
- **v0.5**: Category theory bridges between domains
- **v1.0**: Full mathematical completeness across all 11 domains

## Dependencies

ArithmoPraxis is designed as **infrastructure** - other IELs depend on it, but it has minimal dependencies:
- Coq Standard Library
- PXL foundations (when available)
- No external mathematical libraries (self-contained)

## Contact & Support

- **Technical Issues**: See `tests/arithmo_suite.v` for usage examples
- **Performance**: Run `scripts/bench.sh` for baseline measurements
- **Extension**: Each domain has individual README with expansion guidelines
- **Integration**: Use `Meta/SIGNALS.v` interface contracts for cross-IEL calls

**ArithmoPraxis provides the mathematical foundation for LOGOS's vision of provably trustworthy AGI with mathematical reasoning capabilities.**
