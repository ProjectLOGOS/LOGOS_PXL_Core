# Compatibilism Domain API

## Overview

The Compatibilism domain models the philosophical position that free will and determinism can coexist within temporal logic frameworks. It provides formal structures for reasoning about agent freedom, causal necessity, and their compatibility in temporal contexts.

## What It Models

**In Plain English**: This domain answers questions like "Can an agent act freely even when their actions are causally determined?" and "How do we reconcile moral responsibility with temporal causation?" It models agents making choices within temporal constraints while maintaining both freedom and causal necessity.

## Core Types

### `Agent`
- **Structure**: `Record Agent := { agent_id : nat }`
- **Purpose**: Represents a moral agent capable of making free choices
- **Usage**: Each agent has a unique identifier for tracking across temporal contexts

### `Action`
- **Type**: Abstract parameter type
- **Purpose**: Represents temporal actions performed by agents
- **Future**: Will be integrated with ChronoPraxis temporal propositions

### `Free : Agent -> Action -> Prop`
- **Current**: `Definition Free (_:Agent) (_:Action) : Prop := True`
- **Purpose**: Defines when an agent acts freely on an action
- **Future**: Will integrate with χ_A (agent time) temporal propositions

### `Necessary : Action -> Prop`
- **Type**: Parameter predicate
- **Purpose**: Defines causal necessity for actions
- **Future**: Will integrate with χ_C (cosmic time) temporal propositions

## Key Theorems

### `compatibilist_consistency`
- **Statement**: `forall (a : Agent) (act : Action), Free a act -> Necessary act -> Free a act`
- **Meaning**: An agent can act freely even when the action is causally necessary
- **Status**: Parameter placeholder, will be proven constructively

### `temporal_freedom_preservation`
- **Statement**: `forall (a : Agent) (act : Action), Free a act -> Free a act`
- **Meaning**: Freedom is preserved across temporal projections
- **Status**: Currently identity, will use ChronoMappings

## Example Queries

### Query 1: Agent Freedom Analysis
```coq
(* Check if a specific agent can act freely on a given action *)
Definition can_act_freely (a : Agent) (act : Action) : Prop :=
  Free a act.

(* Example: Agent with ID 42 acting on some action *)
Check can_act_freely {| agent_id := 42 |} act.
```

### Query 2: Compatibilist Consistency Check
```coq
(* Verify that freedom and necessity are compatible for an agent-action pair *)
Definition freedom_necessity_compatible (a : Agent) (act : Action) : Prop :=
  Free a act -> Necessary act -> Free a act.

(* This should always hold due to compatibilist_consistency *)
Check freedom_necessity_compatible.
```

## Integration Points

- **ChronoPraxis Substrate**: Will integrate with χ_A, χ_B, χ_C temporal mappings
- **Temporal Logic**: Agent choices will be embedded in temporal proposition spaces
- **Modal Logic**: Connections to possible worlds through temporal accessibility
- **Physics Integration**: Causal necessity will relate to physical determinism

## Semantics v1: Constructive Freedom

### Core Insight
**Free(a, pA)** means: there exists pA' different in χ_A that becomes the same eternal content in χ_C.

**Practical Reading**: The agent has at least two χ_A-realizations (lived temporal experiences) that collapse to one timeless truth in χ_C (cosmic time). Freedom is the existence of such an alternative - multiple ways to experience time that lead to the same eternal outcome.

### Constructive Definition
```coq
Definition alt (pA pA' : PA) : Prop :=
  pA <> pA' /\ A_to_C pA = A_to_C pA'.

Definition Free (_:Agent) (pA:PA) : Prop :=
  exists pA', alt pA pA'.
```

### First Proven Theorem
**`freedom_preserved_via_ABA`**: Freedom survives temporal coordinate transformations (A→B→A round trips). This uses the bijection properties of ChronoPraxis temporal mappings to show that alternatives remain alternatives under coordinate changes.

## Development Status

- ✅ Basic type structure defined
- ✅ **Constructive freedom semantics implemented**
- ✅ **First non-trivial theorem proven constructively**
- 🔄 Integration with ChronoPraxis substrate in progress
- 🔄 Temporal mapping properties (placeholders → ChronoPraxis imports)
- ⏳ Comprehensive test coverage needed
- ⏳ Real-world compatibility examples needed
