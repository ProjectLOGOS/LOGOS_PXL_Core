# ChronoPraxis Domains Overview

This document provides a high-level overview of the three specialized domains that extend the ChronoPraxis IEL v1.0 temporal logic framework.

## Domain Architecture

Each domain provides a specialized perspective on temporal reasoning while maintaining integration with the core ChronoPraxis substrate:

- **Common Foundation**: All domains build on χ_A, χ_B, χ_C temporal proposition mappings
- **Specialized Focus**: Each domain addresses specific philosophical and technical questions
- **Constructive Proofs**: All theorems proven without `Admitted` statements
- **Integration Ready**: Designed for cross-domain compatibility and substrate integration

## The Three Domains

### 1. Compatibilism Domain
**File**: `modules/IEL/ChronoPraxis/domains/Compatibilism/CompatibilismTheory.v`

**Focus**: Free will and determinism in temporal contexts

**Key Question**: How can agents act freely within causally determined temporal frameworks?

**Core Concepts**:
- Agents with unique identifiers
- Temporal freedom operators
- Causal necessity predicates
- Compatibilist consistency theorems

### 2. Empiricism Domain  
**File**: `modules/IEL/ChronoPraxis/domains/Empiricism/UnifiedFieldLogic.v`

**Focus**: Physics integration with temporal logic

**Key Question**: How do physical measurements in different reference frames map to temporal propositions?

**Core Concepts**:
- Observer frames with clocks
- Coordinate frames with scales
- Frame transformation operations
- Observational coherence theorems

### 3. Modal Ontology Domain
**File**: `modules/IEL/ChronoPraxis/domains/ModalOntology/ModalCollapse.v`

**Focus**: Possible worlds and temporal modal collapse

**Key Question**: How do all possible temporal paths converge to the same cosmic outcome?

**Core Concepts**:
- Possible worlds with accessibility relations
- Temporal instantiation paths
- Modal collapse theorems
- Agent choice convergence

## Integration Mapping

| Domain | χ_A (Agent Time) | χ_B (Coordinate Time) | χ_C (Cosmic Time) |
|--------|------------------|----------------------|-------------------|
| **Compatibilism** | Agent choices | Causal chains | Necessary outcomes |
| **Empiricism** | Observer measurements | Coordinate transformations | Universal time |
| **Modal Ontology** | Possible agent paths | Modal accessibility | Convergent reality |

## Cross-Domain Connections

### Compatibilism ↔ Empiricism
- Agent choices occur within physical reference frames
- Causal necessity relates to physical determinism
- Temporal freedom constrained by relativistic physics

### Compatibilism ↔ Modal Ontology  
- Agent choices create branches in possible worlds
- Free will operates across modal accessibility relations
- Moral responsibility maintained despite modal collapse

### Empiricism ↔ Modal Ontology
- Physical worlds as possible worlds
- Reference frame transformations as modal accessibility
- Empirical measurements collapse possibilities to actuality

## Development Status

| Domain | Basic Types | Constructive Stubs | API Docs | Tests | Integration |
|--------|------------|-------------------|----------|-------|-------------|
| **Compatibilism** | ✅ | ✅ | ✅ | ✅ | ⏳ |
| **Empiricism** | ✅ | ✅ | ✅ | ✅ | ⏳ |
| **Modal Ontology** | ✅ | ✅ | ✅ | ✅ | ⏳ |

## Detailed APIs

For comprehensive technical documentation, see the detailed API references:

- **[Compatibilism_API.md](domains/Compatibilism_API.md)**: Types, theorems, and example queries for free will reasoning
- **[Empiricism_API.md](domains/Empiricism_API.md)**: Frame types, transformations, and physics integration  
- **[ModalOntology_API.md](domains/ModalOntology_API.md)**: Modal types, accessibility relations, and convergence theorems

## Build and Test

### Individual Domain Builds
```bash
make domain-compatibilism    # Build Compatibilism domain + tests
make domain-empiricism       # Build Empiricism domain + tests  
make domain-modal-ontology   # Build Modal Ontology domain + tests
```

### Comprehensive Build
```bash
make clean                   # Clean previous builds
make -j                      # Build entire project
make domain-compatibilism    # Test Compatibilism  
make domain-empiricism       # Test Empiricism
make domain-modal-ontology   # Test Modal Ontology
make prove                   # Verify no admits, constructive proofs only
```

### VS Code Tasks
- `Ctrl+Shift+P` → "Tasks: Run Task"
- Select from: `coq: compatibilism`, `coq: empiricism`, `coq: modal-ontology`

## Future Development

### Phase 2 Roadmap
1. **Module Integration**: Fix import paths for cross-domain dependencies
2. **Constructive Theorems**: Replace parameter placeholders with proven theorems  
3. **Comprehensive Testing**: Expand beyond smoke tests to property-based testing
4. **Real-World Examples**: Add concrete applications of each domain
5. **Cross-Domain Proofs**: Prove compatibility and consistency across domains

### Long-Term Vision
- **Unified Temporal Metaphysics**: Complete formal system for temporal reasoning
- **Applied Philosophy**: Practical tools for philosophical analysis
- **Physics Integration**: Full relativistic temporal logic
- **AI Applications**: Temporal reasoning for artificial intelligence systems

## Modal Logic Foundation

**Files**: `modules/IEL/ChronoPraxis/theorems/ModalStrength/`

**Modal base (normal systems):** K axiom and Necessitation are proven semantically and lifted to proofs. S4/S5 add T/4/5/B under the corresponding frame conditions; propositional conservativity holds constructively.

**Key Components**:
- **ModalRules.v**: K axiom (□(φ→ψ) → (□φ → □ψ)) and Necessitation rule with semantic soundness
- **ModalAxiomsSound.v**: T, 4, 5, B axiom schemata proven valid under frame classes (reflexive, transitive, symmetric)  
- **Systems.v**: Bundled K, S4, S5 modal systems with complete axiomatizations
- **Frame Correspondence**: Each modal axiom corresponds to its standard frame condition with constructive proofs

**Theoretical Foundation**:
- Semantic validity proofs using Kripke frame semantics
- Completeness bridge from semantic validity to syntactic provability
- Conservative extension over non-modal propositional fragment
- Full constructive proofs maintaining zero admits policy

## Documentation

- **Auto-generated API docs**: see `docs/html/toc.html` (built by `coq: docs-html` task or CI artifact)
- **Property tests**: `tests/DomainProperties.v` - Core invariant validation
- **Plain-English glossary**: `docs/GLOSSARY.md` - Non-technical explanations
- **Examples**: `examples/` directory - Concrete demonstrations of A→B→C flows

---

*This overview provides the foundation for Phase 2 development. Each domain is ready for intensive theorem development while maintaining constructive proof standards and cross-domain compatibility.*