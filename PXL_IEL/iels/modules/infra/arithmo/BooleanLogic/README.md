# Boolean Logic Domain

## Scope
Constructive Boolean logic, SAT solving, decision procedures, and propositional reasoning for LOGOS modal systems.

## Planned Modules

### Core Boolean Theory
- [ ] `Props.v` - Propositions, constructive connectives (∧, ∨, →, ¬)
- [ ] `Classical.v` - LEM bridges, double negation elimination
- [ ] `Decidability.v` - Decidable predicates, Boolean reflection

### SAT and Decision Procedures
- [ ] `CNF.v` - Conjunctive normal forms, conversion algorithms
- [ ] `DPLL.v` - Davis-Putnam-Logemann-Loveland SAT solver
- [ ] `Resolution.v` - Resolution method for propositional logic
- [ ] `BDD.v` - Binary decision diagrams for efficient Boolean functions

### Modal Boolean Integration
- [ ] `ModalProps.v` - □P, ◇P for Boolean propositions
- [ ] `BooleanModal.v` - S4/S5 modal Boolean logic
- [ ] `Completeness.v` - Soundness/completeness for modal Boolean systems

### Applications
- [ ] `Circuits.v` - Boolean circuit verification
- [ ] `Planning.v` - STRIPS-style Boolean planning
- [ ] `ModelChecking.v` - Propositional model checking

## TODO Checklist

### Phase 1: Foundation (v0.4)
- [ ] Implement `Props.v` with constructive Boolean operations
- [ ] Add `Decidability.v` for Boolean reflection lemmas
- [ ] Create basic SAT solver in `DPLL.v`
- [ ] Write property-based tests for Boolean operations

### Phase 2: Decision Procedures (v0.5)
- [ ] Complete CNF conversion algorithms
- [ ] Implement efficient BDD operations
- [ ] Add resolution-based theorem proving
- [ ] Benchmark SAT solver performance

### Phase 3: Modal Integration (v0.6)
- [ ] Bridge Boolean logic with Core/ModalWrap.v
- [ ] Implement modal Boolean completeness proofs
- [ ] Add modal SAT procedures
- [ ] Create LOGOS planning interface

### Phase 4: Applications (v0.7)
- [ ] Circuit verification examples
- [ ] Model checking for finite state systems
- [ ] Planning domain integration
- [ ] Performance optimization

## Dependencies
- `IEL.ArithmoPraxis.Core.ModalWrap` - Modal operators □/◇
- `IEL.ArithmoPraxis.Meta.Realizability` - Constructive bridges
- Coq standard library `Logic`, `Bool`, `List`

## Integration Points
- **Planning IEL**: Boolean constraint satisfaction
- **Verification IEL**: Propositional model checking
- **Modal Reasoning IEL**: Boolean modal logic substrate

## Performance Goals
- SAT solving: Handle formulas with 1000+ variables
- BDD operations: Support Boolean functions of 50+ variables
- Modal reasoning: Efficient □/◇ Boolean computations
- Decision procedures: Sub-second response for typical queries

## Related Domains
- **ConstructiveSets**: Boolean algebras as sets
- **CategoryTheory**: Boolean topoi and Heyting algebras
- **TypeTheory**: Propositions-as-types correspondence
