# ModalPraxis: Unified Modal Logic Framework

**Formerly UM-Internal Emergent Logics (Unified Modal - Intuitionistic Epistemic Logic)**

## Overview

**Idea:** One interface covers K/T/S4/S5/KD/KB by toggling frame laws (Serial, Reflexive, Symmetric, Transitive, Euclidean).
**Guarantees:** K + Necessitation always; T/4/5/B/D under flags; propositional conservativity holds.

**Why constructive:** All validities are proved semantically and lifted via the kernel completeness theorem; no new axioms.

**Use:** Import `Systems.v`, provide frame-law proofs/assumptions, and you get the corresponding axiom schemata and rules.

## Architecture

### Core Framework
- **FrameSpec.v**: Parameterized frame classes (Serial, Reflexive, Symmetric, Transitive, Euclidean)
- **NormalBase.v**: K axiom and Necessitation rule - valid on all frames
- **DerivedAxioms.v**: T, 4, 5, B, D axioms under their corresponding frame conditions
- **Systems.v**: Bundled modal logic systems (K, T, S4, S5, KD, KB)
- **Conservativity.v**: Proofs that modal extensions are conservative over modal-free formulas

### Modal Systems Hierarchy

```
K System: K axiom + Necessitation
    ↓
T System: K + T (reflexive frames)
    ↓
S4 System: K + T + 4 (reflexive + transitive frames)
    ↓
S5 System: K + T + 5 (equivalence frames: reflexive + symmetric + transitive)

Parallel branches:
KD System: K + D (serial frames)
KB System: K + B (symmetric frames)
```

### Frame Correspondence

| Axiom | Formula | Frame Condition |
|-------|---------|----------------|
| **K** | □(φ→ψ) → (□φ → □ψ) | No conditions (valid on all frames) |
| **T** | □φ → φ | Reflexive: ∀w. R w w |
| **4** | □φ → □□φ | Transitive: ∀w,u,v. R w u → R u v → R w v |
| **5** | ◇φ → □◇φ | Equivalence: Reflexive + Symmetric + Transitive |
| **B** | φ → □◇φ | Symmetric: ∀w,u. R w u → R u w |
| **D** | □φ → ◇φ | Serial: ∀w. ∃u. R w u |

## Implementation Features

### Constructive Proofs Only
- **Zero Admits Policy**: All theorems proven constructively without `Admitted`
- **Semantic Approach**: Validity proven using Kripke frame semantics, then lifted to provability
- **Completeness Bridge**: Uses existing PXL completeness theorem to connect semantics and syntax

### Parameterized Frame Laws
- **Class-Based**: Each frame property (Serial, Reflexive, etc.) is a Coq class
- **Toggle-able**: Systems can be instantiated with any combination of frame properties
- **Compositional**: Complex systems (like S5) built from simpler components

### Conservative Extension
- **Propositional Conservativity**: Modal systems don't prove new non-modal theorems
- **Consistency Preservation**: Modal axioms don't introduce contradictions in propositional reasoning
- **Modular Design**: Each axiom proven only under its required frame conditions

## Usage Examples

### Basic K System
```coq
From ModalPraxis Require Import Systems.
Module MyLogic := KSystem.
Check MyLogic.K_available.  (* K axiom available *)
```

### S4 System with Frame Conditions
```coq
Module MyS4Logic := S4System.
Check MyS4Logic.S4_T_available.  (* T axiom: □φ → φ *)
Check MyS4Logic.S4_4_available.  (* 4 axiom: □φ → □□φ *)
```

### Custom System with Specific Frame Properties
```coq
Section MyCustomSystem.
  Context (Hrefl: Reflexive) (Hsym: Symmetric).

  (* Gets T axiom from reflexivity *)
  Check provable_T.
  (* Gets B axiom from symmetry *)
  Check provable_B.
End MyCustomSystem.
```

## File Organization

```
modules/Internal Emergent Logics/UM/
├── modal/
│   └── FrameSpec.v          # Core frame specifications and classes
└── theorems/
    ├── NormalBase.v         # K axiom and Necessitation
    ├── DerivedAxioms.v      # T, 4, 5, B, D under frame conditions
    ├── Systems.v            # Bundled modal systems
    └── Conservativity.v     # Conservative extension proofs

tests/
└── UMIEL_Tests.v           # Comprehensive tests for all systems
```

## Integration with ChronoPraxis

### Complementary to Existing Modal Infrastructure
- **ChronoPraxis Modal**: Domain-specific modal reasoning for temporal logic
- **UM-Internal Emergent Logics**: General-purpose modal logic foundation with frame parameterization
- **Shared Foundation**: Both use PXL kernel completeness and constructive proof standards

### Unified Temporal-Modal Reasoning
UM-Internal Emergent Logics provides the logical foundation that ChronoPraxis domains can build upon:
- **Compatibilism**: Agent choice modalities with appropriate frame conditions
- **Empiricism**: Observer-relative modal operators for measurement contexts
- **Modal Ontology**: Possible world accessibility for temporal path analysis

## Future Extensions

### Additional Modal Axioms
- **G (Löb)**: □(□φ → φ) → □φ
- **M**: □◇φ → ◇□φ
- **H**: ◇□φ → □◇φ
- **Grz**: □(□(φ → □φ) → φ) → φ

### Multi-Modal Systems
- **Temporal Logic**: Separate operators for past/future with linear/branching time
- **Epistemic Logic**: Knowledge and belief operators with different accessibility relations
- **Deontic Logic**: Obligation and permission modalities

### Integration Capabilities
- **Cross-Domain**: Modal operators shared between ChronoPraxis domains
- **Parameterized Time**: Frame conditions that vary with temporal contexts
- **Physics Integration**: Modal operators constrained by relativistic frame transformations

---

*UM-Internal Emergent Logics provides a unified, constructive foundation for modal reasoning that complements ChronoPraxis while maintaining the project's commitment to rigorous formal verification.*
