# ModalPraxis: Unified Modal Logic Framework

**Formerly UM-IEL (Unified Modal - Intuitionistic Epistemic Logic)**

## Overview

ModalPraxis is a unified modal logic framework that provides a systematic approach to modal reasoning by parameterizing frame properties. It serves as the foundational modal logic layer within the IEL (Intuitionistic Epistemic Logic) taxonomy.

## Architecture

### Core Components

- **Frame Specification** (`modal/FrameSpec.v`): Parameterized frame classes with PXL canonical model integration
- **Normal Base** (`theorems/NormalBase.v`): K axiom and Necessitation rule valid on all frames  
- **Derived Axioms** (`theorems/DerivedAxioms.v`): T, 4, 5, B, D axioms under conditional frame properties
- **Modal Systems** (`theorems/Systems.v`): Bundled K/T/S4/S5/KD/KB modal systems with hierarchical organization
- **Conservativity** (`theorems/Conservativity.v`): Conservative extension proofs over modal-free formulas

### Frame Property Classes

ModalPraxis uses Coq type classes to parameterize frame properties:

```coq
Class Serial     : Prop := serial_R     : forall w, exists u, can_R w u.
Class Reflexive  : Prop := reflexive_R  : forall w, can_R w w.
Class Symmetric  : Prop := symmetric_R  : forall w u, can_R w u -> can_R u w.
Class Transitive : Prop := transitive_R : forall w u v, can_R w u -> can_R u v -> can_R w v.
Class Euclidean  : Prop := euclid_R     : forall w u v, can_R w u -> can_R w v -> can_R u v.
```

### Modal Systems Hierarchy

- **K**: Base normal modal logic (all frames)
- **T**: K + Reflexive frames (T axiom: □φ → φ)
- **S4**: T + Transitive frames (+ 4 axiom: □φ → □□φ)
- **S5**: S4 + Symmetric frames (+ B axiom: φ → □◊φ, + 5 axiom: ◊φ → □◊φ)
- **KD**: K + Serial frames (D axiom: □φ → ◊φ)
- **KB**: K + Symmetric frames (B axiom: φ → □◊φ)

## Integration with ChronoPraxis

ModalPraxis provides the theoretical foundation for ChronoPraxis temporal modal systems:

- **S4 Overlay Integration**: ChronoPraxis S4 systems proven equivalent to ModalPraxis S4 instances
- **S5 Overlay Integration**: ChronoPraxis S5 systems proven equivalent to ModalPraxis S5 instances
- **Bidirectional Equivalence**: Complete theorem derivation in both directions
- **Conservative Extension**: All integrations maintain constructive proof policy (zero admits)

## Key Theorems

### Normal Base (K + Necessitation)
- `provable_K`: K axiom valid on all frames
- `provable_necessitation`: Necessitation rule for universal validities

### Derived Axioms (Frame-Conditional)
- `provable_T`: T axiom under Reflexive + Transitive frames
- `provable_4`: 4 axiom under Reflexive + Transitive frames  
- `provable_B`: B axiom under Symmetric + Transitive + Reflexive frames
- `provable_5`: 5 axiom under Symmetric + Transitive + Reflexive frames
- `provable_D`: D axiom under Serial frames

### System Bundling
- Complete modal systems with hierarchical inclusion relationships
- Automated theorem derivation based on frame property satisfaction
- Modular composition for custom modal logics

## Usage Patterns

### Basic Modal Reasoning
```coq
(* K axiom applies to all modal contexts *)
apply provable_K.

(* Necessitation for universal truths *)
apply provable_necessitation. exact H_universal_validity.
```

### Frame-Conditional Reasoning
```coq
(* T axiom requires reflexive + transitive frames *)
Context (Hrefl: Reflexive) (Htran: Transitive).
apply (provable_T Hrefl Htran).

(* S5 features require reflexive + symmetric + transitive frames *)
Context (Hrefl: Reflexive) (Hsym: Symmetric) (Htran: Transitive).
apply (provable_B Hsym Htran Hrefl).
apply (provable_5 Hsym Htran Hrefl).
```

### System Integration
```coq
(* Access bundled S4 system *)
From ModalPraxis Require Import Systems.
Check S4_system.

(* Use conservativity results *)
From ModalPraxis Require Import Conservativity.
apply modal_conservative_extension.
```

## Design Principles

1. **Parameterized Abstraction**: Frame properties as explicit parameters enable precise modal reasoning
2. **Constructive Foundations**: All theorems proven constructively without axiom admits
3. **Modular Composition**: Systems built compositionally from frame property combinations
4. **Integration Ready**: Designed for seamless integration with existing modal systems
5. **Canonical Models**: Built on PXL canonical model construction for semantic grounding

## File Organization

```
modules/IEL/ModalPraxis/
├── modal/
│   └── FrameSpec.v          # Frame property classes and canonical models
└── theorems/
    ├── NormalBase.v         # K axiom and Necessitation rule
    ├── DerivedAxioms.v      # T, 4, 5, B, D axioms with frame conditions
    ├── Systems.v            # Bundled modal systems (K, T, S4, S5, KD, KB)
    └── Conservativity.v     # Conservative extension proofs
```

## Verification Status

✅ **Complete Implementation**: All core modal systems implemented and verified  
✅ **Zero Admits Policy**: All theorems proven constructively without admitted axioms  
✅ **ChronoPraxis Integration**: Equivalence with existing temporal modal overlays proven  
✅ **Comprehensive Testing**: Full test suite with 18/18 integration tests passing  
✅ **Documentation**: Complete API documentation and usage examples  

## Future Extensions

- **Epistemic Modalities**: Integration with knowledge and belief operators
- **Temporal Extensions**: Native temporal modal operators beyond S4/S5  
- **Hybrid Logic**: Nominal-enriched modal reasoning
- **Many-Dimensional Modal Logic**: Multiple accessibility relations
- **Dynamic Logic**: Program modal logic integration

---

**ModalPraxis** represents the evolution of modal logic foundations within the LOGOS-PXL system, providing a robust, extensible, and theoretically sound basis for all modal reasoning tasks.