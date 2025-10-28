# Axiom Removal Plan

## Overview
Replace infra axioms with constructive proofs using typeclasses and instances derived from PXL lemmas or prior theorems. Aim for zero axioms in infra.

## Strategies

### Option 1: Weaken to Derivable Form
For axioms that can be proven from PXL + existing interfaces, replace with Theorem proofs.

### Option 2: Typeclass Capability
Introduce typeclasses (e.g., Cap_ChiReflexive) with instances in infra/Core.v, discharging via PXL lemmas.

### Option 3: Functor Pattern
Refactor interfaces to accept hypotheses as module parameters, proving instances in infra.

## Per Axiom Plans

- **chi_reflexivity**: Option 2. Add Cap_ChiReflexive typeclass, instance proves m = m using PXL equality or inductive properties.
- **tau_reflexive**: Option 2. Cap_TauReflexive, instance from PXL order theory.
- **tau_antisymmetric**: Option 2. Cap_TauAntisymmetric.
- **tau_transitive**: Option 2. Cap_TauTransitive.
- **chi_distinction**: Option 1. If chi_A, chi_B, chi_C are distinct constructors, prove directly.
- **forces_Box/Dia/Impl**: Option 3. Move to module parameters in ModalPraxis interface.
- **Others**: Similar typeclass approach, derive from PXL soundness.

## Implementation Order
1. Reflexivity axioms (chi_reflexivity, tau_reflexive).
2. Order axioms (antisymmetric, transitive).
3. Modal forces axioms.
4. Mappings and projections.

## Risks
- May require extending PXL interfaces if not derivable.
- Proof complexity increase; monitor coqchk times.