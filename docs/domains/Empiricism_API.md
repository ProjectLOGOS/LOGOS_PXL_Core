# Empiricism Domain API

## Overview

The Empiricism domain models the integration of physics with temporal logic, providing formal structures for mapping between observer frames, coordinate systems, and eternal temporal references. It bridges empirical measurement with the ChronoPraxis temporal proposition system.

## What It Models

**In Plain English**: This domain answers questions like "How do physical measurements in different reference frames relate to temporal logic propositions?" and "How do we formally connect Einstein's relativity with temporal reasoning?" It models the relationship between physical reality and temporal logic through frame transformations.

## Frame Mappings

- **χ_A (Agent Time)** ↔ **LocalTime**: Observer's proper time measurements
- **χ_B (Coordinate Time)** ↔ **CoordinateTime**: Coordinate system time measurements  
- **χ_C (Cosmic Time)** ↔ **CosmicTime**: Universal/eternal time reference

## Core Types

### `ObserverFrame`
- **Structure**: `Record ObserverFrame := { obs_clock : nat }`
- **Purpose**: Represents local observer with clock for measuring proper time
- **Usage**: Models individual observers making temporal measurements
- **Integration**: Maps to χ_A temporal propositions

### `CoordinateFrame`
- **Structure**: `Record CoordinateFrame := { coord_scale : nat }`
- **Purpose**: Represents coordinate system with scale for spacetime measurements
- **Usage**: Models reference frames for physics calculations
- **Integration**: Maps to χ_B temporal propositions

### `EternalFrame`
- **Type**: Abstract parameter type
- **Purpose**: Represents cosmic/eternal reference frame
- **Usage**: Universal temporal reference point
- **Integration**: Maps to χ_C temporal propositions

## Temporal Types

### `LocalTime`
- **Purpose**: Agent/observer time measurements (χ_A)
- **Usage**: Proper time as measured by local observers

### `CoordinateTime`
- **Purpose**: Coordinate frame time measurements (χ_B)
- **Usage**: Time as measured in specific coordinate systems

### `CosmicTime`
- **Purpose**: Eternal/cosmic time reference (χ_C)
- **Usage**: Universal temporal backdrop

## Transformation Operations

### `local_to_coordinate : LocalTime -> CoordinateTime`
- **Purpose**: Transform from observer proper time to coordinate time
- **Physics**: Relates to Lorentz transformations

### `coordinate_to_cosmic : CoordinateTime -> CosmicTime`
- **Purpose**: Transform from coordinate time to cosmic time
- **Physics**: Relates to cosmological time scales

### `local_to_cosmic : LocalTime -> CosmicTime`
- **Purpose**: Direct transformation from local to cosmic time
- **Physics**: Complete temporal embedding

## Key Theorems

### `observational_coherence`
- **Statement**: `forall (lt : LocalTime), local_to_cosmic lt = coordinate_to_cosmic (local_to_coordinate lt)`
- **Meaning**: Direct path A→C equals composed path A→B→C
- **Physics**: Consistency of temporal transformations
- **Status**: Parameter placeholder, will be proven constructively

## Example Query

### Physics-Temporal Mapping
```coq
(* Model a physics experiment with observer and coordinate frame *)
Definition physics_experiment (obs : ObserverFrame) (coord : CoordinateFrame) : Prop :=
  (* Observer measures local time using their clock *)
  let local_measurement := obs.(obs_clock) in
  (* Coordinate system provides scaling for measurements *)
  let coord_scaling := coord.(coord_scale) in
  (* Both measurements should be coherent when mapped to cosmic time *)
  True. (* Placeholder for actual coherence check *)

Example experiment_coherence :
  physics_experiment {| obs_clock := 100 |} {| coord_scale := 1000 |} = True.
Proof. reflexivity. Qed.
```

## Integration Points

- **Special Relativity**: Frame transformations model Lorentz transformations
- **General Relativity**: Coordinate frames handle curved spacetime
- **Quantum Mechanics**: Observer measurements in temporal contexts
- **Cosmology**: Eternal frames provide universal temporal reference
- **ChronoPraxis**: Direct mapping to χ_A, χ_B, χ_C temporal propositions

## Constructive Frame Morphisms v1

### Core Insight
**Observational coherence**: measuring A then projecting to C matches going A→C directly. This means local clocks and shared coordinates agree about timeless content.

### Constructive Measurement Functions
```coq
(* Observer measures proper time and projects to coordinate time *)
Definition measure_AB (_:ObserverFrame) (pA:PA) : PB := A_to_B pA.

(* Coordinate frame projects to cosmic/eternal time reference *)
Definition project_BC (_:CoordinateFrame) (pB:PB) : PC := B_to_C pB.

(* Direct measurement from observer to cosmic time *)
Definition measure_AC (_:ObserverFrame) (pA:PA) : PC := A_to_C pA.
```

### First Proven Theorem
**`observational_coherence_frames`**: For any observer and coordinate frame, indirect measurement (A→B→C) equals direct measurement (A→C). This uses the functoriality property of temporal mappings.

**Physical Interpretation**: Your local clock measurement, when translated through coordinate systems to cosmic time, gives the same result as directly embedding your measurement in eternal time. Different measurement paths converge to the same universal truth.

## Relativity Module (NEW)

### Overview
- **Relativity scaffold (v1):** Introduces an abstract χ_B "metric" via an invariant `Inv : PB -> PC`. Any χ_B bijection that preserves `Inv` is an isometry. If `B→C = Inv`, then projection is frame-independent for all isometries, subsuming Lorentz as a special case.

### Key Concepts

#### MetricB Record
```coq
Record MetricB := {
  Inv : PB -> PC;  (* GR-invariant content leading to χ_C *)
}.
```

**Plain English**: Think of `Inv` as the "physical essence" extractor. Given any coordinate time measurement in χ_B, it extracts the truly invariant content that survives coordinate transformations and maps to eternal time χ_C.

#### Isometry Record  
```coq
Record Isometry (M:MetricB) := {
  iso : Bijection PB PB;
  inv_pres : forall pB, Inv M (forward iso pB) = Inv M pB
}.
```

**Plain English**: An isometry is a coordinate transformation (bijection) on χ_B that preserves the physical essence. When you transform a coordinate time measurement, the invariant content `Inv` remains unchanged - this is what makes it a valid physics transformation.

#### ProjectionCompatible Class
```coq
Class ProjectionCompatible (M:MetricB) : Prop :=
  proj_eq_inv : forall pB, B_to_C pB = Inv M pB.
```

**Plain English**: This interface law says that ChronoPraxis's existing B→C temporal projection should agree with the metric's invariant extractor. When this holds, the temporal logic aligns with the physics.

### Core Theorems

#### Frame Independence
```coq
Theorem frame_independence_isometry :
  forall (M:MetricB) (Hpc:ProjectionCompatible M) (T:Isometry M),
    B_to_C (forward (iso T) pB) = B_to_C pB.
```

**Plain English**: If your coordinate transformation is a valid isometry (preserves the physical essence), then transforming χ_B and then projecting to χ_C gives the same result as projecting directly. Physics transformations don't change the eternal time content.

#### Lorentz Generalization  
The existing Lorentz transformations become special cases: if your Lorentz transform preserves `Inv`, it automatically inherits all the frame-independence theorems.

### Why This Keeps Proofs Constructive

1. **No Real Numbers**: `Inv` is completely abstract - no analysis, no limits, no non-constructive geometry
2. **Interface-Driven**: All theorems are conditional on explicit interface assumptions (`ProjectionCompatible`)
3. **Algorithmic**: The invariant preservation is a concrete equality check, not an existential statement
4. **Parameterized**: No global axioms - everything parameterized by the metric structure

This approach lets us capture the essential structure of general relativity (coordinate transformations preserving physical content) while staying completely within constructive mathematics.

## Development Status

- ✅ Basic frame structure defined
- ✅ Temporal type placeholders in place  
- ✅ **Constructive measurement functions implemented**
- ✅ **Observational coherence theorem proven constructively**
- ✅ **Lorentz semantics with frame-independence proven**
- ✅ **GR-ready metric/isometry interface implemented**
- ✅ **Abstract invariant-preserving transformations formalized**
- 🔄 Integration with full ChronoPraxis module system
- ⏳ Concrete physics examples (Minkowski, Schwarzschild metrics)
- ⏳ Spacetime metric integration