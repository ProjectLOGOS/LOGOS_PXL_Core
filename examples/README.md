# ChronoPraxis Examples

This directory contains three concrete examples demonstrating the temporal logic framework across different philosophical domains.

## Examples

### 1. Compatibilism_CoffeeTea.v
**Domain**: Free will within deterministic frameworks  
**Scenario**: Coffee vs tea choice  
**Key Insight**: Shows how different lived experiences (χ_A) can map to the same eternal outcome (χ_C), enabling genuine freedom within determinism.

**Theorems**:
- `free_coffee_example`: Agent is free when choosing coffee because tea is a genuine alternative
- `free_tea_example`: Similarly free when choosing tea

### 2. Empiricism_LabClock.v  
**Domain**: Physics integration through observational coherence  
**Scenario**: Lab measurement of reaction time  
**Key Insight**: Personal experience ("felt like forever") and physics measurement ("2.37 seconds") are coherent perspectives on the same eternal event.

**Theorems**:
- `observational_coherence_labclock`: Lived time and measured time map consistently to eternal time
- `specific_coherence`: Frame-dependent validation of measurement coherence

### 3. ModalOntology_Routes.v
**Domain**: Possible worlds and temporal modal collapse  
**Scenario**: Different routes to work  
**Key Insight**: Multiple possible paths in lived time (χ_A) that reach the same outcome demonstrate modal accessibility through temporal collapse.

**Theorems**:
- `route_accessibility`: Eternal outcomes are self-accessible through lived experience
- `home_store_not_accessible`: Different eternal outcomes are not accessible from each other

## Building

```bash
# Compile all examples
make examples

# Or compile individually  
coqc examples/Compatibilism_CoffeeTea.v
coqc examples/Empiricism_LabClock.v
coqc examples/ModalOntology_Routes.v
```

## Understanding the Examples

Each example follows the A→B→C temporal flow:
- **χ_A (Lived Time)**: Personal, subjective experience
- **χ_B (Physics Time)**: Measurable, objective time (when applicable)  
- **χ_C (Eternal Time)**: Unchanging, timeless truth

The examples demonstrate how different temporal perspectives can be coherent and how alternatives in lived time relate to necessities in eternal time.