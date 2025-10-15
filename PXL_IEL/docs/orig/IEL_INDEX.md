# Internally Emergent Logics (Internal Emergent Logics) - ChronoPraxis Tree

## Overview

The ChronoPraxis framework has been restructured under an **Internally Emergent Logics (Internal Emergent Logics)** organizational system. This system recognizes that complex temporal reasoning emerges from the interaction of foundational substrates, tactical operations, core theorems, and interface abstractions.

## Directory Structure

```
modules/Internal Emergent Logics/ChronoPraxis/
├── substrate/          # Foundational definitions and axioms
│   ├── ChronoAxioms.v     # Core temporal axioms
│   ├── Bijection.v        # Constructive bijection interface
│   ├── ChronoMappings.v   # Bijective mappings between modes
│   ├── ChronoAgents.v     # Agent-based temporal constructs
│   └── SmokeTests.v       # Substrate validation tests
├── tactics/            # Operational reasoning procedures
│   └── ChronoTactics.v    # Specialized temporal tactics
├── theorems/           # Core mathematical results
│   ├── ChronoProofs.v     # Main constructive proofs
│   └── MetaTheorems.v     # Emergent meta-theorem registry
├── interfaces/         # High-level API and abstractions
│   └── ChronoPraxis.v     # Main public interface
└── domains/            # Domain-specific specializations
    ├── Compatibilism/     # Free will & determinism
    ├── Empiricism/        # Experience-based reasoning
    └── ModalOntology/     # Modal temporal logics
```

## Internal Emergent Logics Principle

**Internally Emergent Logics** posits that sophisticated reasoning systems emerge from well-structured interactions between:

1. **Substrate**: Foundational axioms and primitive constructs
2. **Tactics**: Operational procedures for manipulation and proof
3. **Theorems**: Proven mathematical results and their constructive evidence
4. **Interfaces**: Abstraction layers that expose functionality
5. **Domains**: Specialized applications to specific problem areas

## Key Internal Emergent Logics Features

### Meta-Theorem Registry (`MetaTheorems.v`)
- `temporal_unification_meta`: Constructive bijections enable unified reasoning
- `constructive_temporal_completeness`: All temporal relations are decidable
- `IEL_meta_registry`: Aggregated emergent theorems for higher-order reasoning

### Constructive Foundations
All ChronoPraxis theorems maintain constructive proof foundations:
- `temporal_convergence`: Constructive proof of mode convergence
- `chronological_collapse_*`: Bijective collapse theorems
- `causal_bijection_*`: Causal relationship preservation
- `temporal_consistency`: Internal consistency validation

### Bijective Core
Three fundamental bijections form the temporal reasoning substrate:
- `map_AB`: Mode A ↔ Mode B constructive mapping
- `map_BC`: Mode B ↔ Mode C constructive mapping
- `map_AC`: Mode A ↔ Mode C direct constructive mapping

## Build System

```bash
# Generate Coq makefile
make Makefile.coq

# Build all modules
make -f Makefile.coq

# Clean build artifacts
make clean
```

## Integration Points

- **VS Code**: Configured with `.vscode/tasks.json` for integrated builds
- **CI/CD**: Hooks available for automated verification
- **Testing**: Comprehensive smoke tests validate substrate integrity

## Domain Extensions

The `domains/` directory provides specialized temporal logic applications:
- **Compatibilism**: Reconciling free will with temporal determinism
- **Empiricism**: Experience-based temporal reasoning patterns
- **ModalOntology**: Modal temporal logics and possible world semantics

## Internal Emergent Logics Tags

All Internal Emergent Logics modules include standardized tags for emergent logic identification:
```coq
(* ===== Internal Emergent Logics TAG: [CATEGORY] ===== *)
```

Categories: `SUBSTRATE`, `TACTICS`, `THEOREMS`, `META-THEOREMS`, `INTERFACES`, `DOMAINS`

## Module Status

- ChronoPraxis status: **Stable (v1.0)** — constructive, zero admits

## Internal Emergent Logics Registry

### Core Internal Emergent Logics Implementations

- **TropoPraxis (TPX)** — unified normal modal systems (K/T/S4/S5/KD/… via frame flags)
- **GnosiPraxis (GPX)** — Epistemic Internal Emergent Logics (knowledge/belief modalities)
- **ThemiPraxis (ThPX)** — Deontic Internal Emergent Logics (obligation/permission modalities)
- **DynaPraxis (DyPX)** — Dynamic Internal Emergent Logics (program execution modalities)
- **HexiPraxis (HxPX)** — Agency Internal Emergent Logics (agent capability modalities)
- **ChremaPraxis (ChPX)** — Resource/Linear Internal Emergent Logics (phase semantics)
- **MuPraxis (MuPX)** — Fixpoint Internal Emergent Logics (μ-calculus over finite frames)
- **TychePraxis (TyPX)** — Probabilistic Internal Emergent Logics (finite rational kernels)

### Status
- ✅ TropoPraxis: v0.1 stub (interfaces only)
- ✅ GnosiPraxis: v0.1 complete (epistemic axioms via ModalPraxis)
- ✅ ThemiPraxis: v0.1 complete (deontic axioms via ModalPraxis)
- ✅ DynaPraxis: v0.1 complete (dynamic axioms via ModalPraxis)
- ✅ HexiPraxis: v0.1 complete (agency axioms via ModalPraxis)
- 🔄 ChremaPraxis: v0.1 stub (interfaces only)
- 🔄 MuPraxis: v0.1 stub (interfaces only)
- 🔄 TychePraxis: v0.1 stub (interfaces only)

---

*For detailed Internal Emergent Logics specifications, see `IELS_SPEC.md`
