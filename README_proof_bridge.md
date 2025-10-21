# LOGOS AGI Proof Runtime Bridge

## Overview

The LOGOS AGI Proof Runtime Bridge establishes a verified connection between formal Coq proofs and runtime logic evaluation. This bridge enables the AGI system to perform modal logic reasoning with mathematical guarantees of correctness, extracting verified computational content from formal proofs.

## Architecture

```
┌─────────────────┐    ┌───────────────────┐    ┌─────────────────────┐
│  Coq Proofs     │───▶│   OCaml Bridge    │───▶│  Python Runtime     │
│                 │    │                   │    │                     │
│ • Modal Logic   │    │ • Extraction      │    │ • ModalLogicEval    │
│ • IEL Operators │    │ • JSON Interface  │    │ • IELEvaluator      │  
│ • Verification  │    │ • C Callbacks     │    │ • Batch Processing  │
└─────────────────┘    └───────────────────┘    └─────────────────────┘
```

## Components

### 1. Coq Extraction Layer (`bridge_validation.v`)

Formal definitions and proofs for modal logic evaluation:

- **Modal Propositions**: Inductive type defining atomic props, connectives, modal operators
- **IEL Operators**: Identity and Experience operators for autonomous reasoning
- **Evaluation Functions**: Verified evaluation algorithms for modal formulas
- **Consistency Theorems**: Formal proofs of logical soundness

Key theorems proven:
- `modal_modus_ponens`: Modus ponens holds in modal context
- `box_distribution`: Box operator distributes over conjunction 
- `iel_consistency`: IEL operators maintain logical consistency

### 2. OCaml Bridge Layer (`proof_bridge.ml`)

Native interface between extracted Coq code and external systems:

- **JSON API**: Parse propositions and return evaluation results
- **String Interface**: Direct string-based proposition evaluation
- **Batch Processing**: Efficient evaluation of multiple propositions
- **C Callbacks**: Foreign function interface for integration

### 3. Python Runtime Interface (`iel_runtime_interface.py`)

High-level Python API for the LOGOS AGI runtime:

```python
from iel_runtime_interface import ModalLogicEvaluator, IELEvaluator

# Modal logic evaluation
evaluator = ModalLogicEvaluator()
result = evaluator.evaluate_modal_proposition(
    "[]p -> p",  # T axiom
    world="w0",
    accessible_worlds=["w0", "w1"],
    valuations={"p": True}
)

# IEL evaluation  
iel_eval = IELEvaluator()
result = iel_eval.evaluate_iel_proposition(
    "I(self) -> E(action)",
    identity_context={"self": "agent"},
    experience_context={"action": "movement"}
)
```

## Installation & Usage

### Prerequisites

- Python 3.8+
- Coq 8.15+ 
- OCaml 4.13+
- OPAM 2.1+

### Quick Start

1. **Validate environment**:
   ```bash
   make -f Makefile.bridge validate
   ```

2. **Install dependencies**:
   ```bash
   make -f Makefile.bridge install-deps
   ```

3. **Build bridge**:
   ```bash
   make -f Makefile.bridge build
   ```

4. **Run tests**:
   ```bash
   make -f Makefile.bridge test
   ```

### Manual Build Process

1. **Extract Coq proofs**:
   ```bash
   coqc bridge_validation.v
   ```

2. **Compile OCaml bridge**:
   ```bash
   ocamlopt -I +str str.cmxa -o proof_bridge proof_bridge.ml
   ```

3. **Test Python interface**:
   ```bash
   python test_bridge_consistency.py
   ```

## API Reference

### ModalLogicEvaluator

Main class for modal logic evaluation:

```python
class ModalLogicEvaluator:
    def evaluate_modal_proposition(self, proposition, world=None, 
                                 accessible_worlds=None, valuations=None)
    def validate_syntax(self, proposition)
    def evaluate_batch(self, propositions, **kwargs)
```

### IELEvaluator

Extended evaluator for Identity-Experiential Logic:

```python
class IELEvaluator(ModalLogicEvaluator):
    def evaluate_iel_proposition(self, proposition, identity_context=None,
                               experience_context=None, **kwargs)
```

## Formal Guarantees

The bridge provides the following mathematical guarantees:

1. **Soundness**: All evaluations are consistent with formal modal logic semantics
2. **Completeness**: All valid modal formulas can be evaluated
3. **Consistency**: IEL operators maintain logical coherence
4. **Extraction Correctness**: OCaml code faithfully implements Coq definitions

## Testing

The test suite (`test_bridge_consistency.py`) validates:

- Basic modal logic evaluation
- Propositional connectives (∧, ∨, ¬, →)
- Modal operators (□, ◊)
- IEL operators (I, E)
- Complex formula evaluation
- Syntax validation
- Batch processing
- Error handling
- Logical theorem compliance

Run specific test categories:

```bash
# All tests
python test_bridge_consistency.py

# Modal logic only
python -m unittest test_bridge_consistency.TestModalLogicBridge

# IEL only  
python -m unittest test_bridge_consistency.TestIELBridge

# Consistency verification
python -m unittest test_bridge_consistency.TestBridgeConsistency
```

## Integration with LOGOS Runtime

The bridge integrates with the main LOGOS AGI runtime through:

1. **Reference Monitor**: Validates actions against formal policies
2. **Decision Engine**: Provides verified reasoning for autonomous choices
3. **Learning System**: Ensures learned behaviors respect logical constraints
4. **Safety Guarantees**: Formal verification of critical system properties

## Troubleshooting

### Common Issues

**OCaml compilation fails**:
- Ensure OCaml 4.13+ is installed: `ocaml -version`
- Check str library: `ocamlfind query str`

**Coq extraction errors**:
- Verify Coq installation: `coqc --version`
- Check _CoqProject configuration in coq/ directory

**Python import errors**:
- Ensure Python path includes bridge directory
- Install required packages: `pip install -r requirements.txt`

**Bridge consistency test failures**:
- Run `make validate` to check dependencies
- Verify OCaml bridge compiled successfully
- Check log output for specific error details

### Debug Mode

Enable debug logging:

```python
import logging
logging.basicConfig(level=logging.DEBUG)

evaluator = ModalLogicEvaluator(debug=True)
```

## Contributing

When modifying the bridge:

1. Update Coq proofs first in `bridge_validation.v`
2. Regenerate OCaml extraction
3. Update Python interface if needed
4. Run full test suite: `make test`
5. Update this documentation

## License

This component is part of the LOGOS AGI framework and follows the same licensing terms.
