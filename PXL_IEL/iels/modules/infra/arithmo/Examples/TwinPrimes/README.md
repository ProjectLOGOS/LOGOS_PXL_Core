# Twin Primes Example

## Overview
ArithmoPraxis twin primes verification and analysis system, modeled after the Goldbach example template.

## Structure

### `Spec.v` - Specification
- **`Twin p`**: Predicate for twin prime (p and p+2 both prime)
- **`TwinCover n`**: Exists twin prime ≤ n
- **Modal variants**: `NecTwin`, `PossTwin`, `NecTwinCover` with □/◇ operators
- **Basic proofs**: `twin_3_5`, `twin_5_7`, `twin_11_13` (some admitted for infrastructure)

### `Extract.v` - Witness Search  
- **`check_twin p`**: Boolean check if p is twin prime
- **`find_twin_upto n`**: Find first twin prime ≤ n
- **`extract_twins_upto n`**: Extract all twin primes ≤ n
- **Soundness**: `check_twin_sound`, `find_twin_sound` lemmas

### `Verify.v` - Verification System
- **`verify_twin p`**: Boolean verification of twin prime claim
- **`TwinCertificate`**: Structured certificate with prime1, prime2, gap, verified flag
- **`verify_range start end`**: Verify all twins in range
- **`count_twins_in_range`**: Count verified twins in range

### `Scan.v` - Counting and Logging
- **`scan_twin N`**: Count twin primes ≤ N (main function)
- **`scan_twin_detailed N`**: Extract pairs (p, p+2) for all twins ≤ N
- **CSV logging**: `twin_csv_log N` generates CSV with header "prime1,prime2,gap,verified"
- **Performance**: `ScanBenchmark` record with timing/memory estimates

## Usage

```coq
From IEL.ArithmoPraxis.Examples.TwinPrimes Require Import Spec Extract Verify Scan.

(* Count twin primes up to 100 *)
Eval vm_compute in (scan_twin 100).

(* Find first twin prime up to 20 *)  
Eval vm_compute in (find_twin_upto 20).

(* Generate CSV log for twins up to 30 *)
Eval vm_compute in (twin_csv_log 30).

(* Verify twins in range 3-20 *)
Eval vm_compute in (verify_range 3 20).
```

## Integration with Core

- **Imports**: Uses `IEL.ArithmoPraxis.Core.Numbers` for `is_prime` and `prime` predicate
- **Modal**: Uses `IEL.ArithmoPraxis.Core.ModalWrap` for necessity/possibility operators
- **Pattern**: Follows same structure as `Examples/Goldbach` for consistency

## Performance Characteristics

| Function | Complexity | Notes |
|----------|------------|-------|
| `scan_twin N` | O(N²) | Uses `is_prime` which is O(√n), scanning N values |
| `check_twin p` | O(√p) | Two primality tests |
| `find_twin_upto N` | O(N²) | Linear search with quadratic primality |
| `verify_range start end` | O((end-start)²) | Range verification |

## Known Twin Primes (for testing)

- **(3, 5)**: First twin prime pair
- **(5, 7)**: Second twin prime pair  
- **(11, 13)**: Third twin prime pair
- **(17, 19)**: Fourth twin prime pair
- **(29, 31)**: Fifth twin prime pair

## Status

- ✅ **Core functions**: `scan_twin`, `check_twin`, `extract_twins_upto` implemented
- ✅ **Verification**: Certificate-based verification system
- ✅ **Logging**: CSV export with proper formatting
- ✅ **Modal integration**: Necessity/possibility variants defined
- 🚧 **Proofs**: Many lemmas admitted for infrastructure (TODO: complete)
- 🚧 **Optimization**: Naive O(N²) implementation (TODO: optimize)

## Future Extensions

### v0.5 Optimizations
- Implement sieve-based twin prime detection
- Add memoization for repeated primality tests
- Optimize range scanning with early termination

### v0.6 Advanced Features  
- Hardy-Littlewood conjecture verification
- Twin prime constant approximation
- Statistical analysis of twin prime gaps

### v0.7 Integration
- Connect to `NumberTheory` domain for advanced results
- Link with `Probability` for statistical analysis
- Bridge to `Optimization` for efficient algorithms

## Relationship to Goldbach Example

The TwinPrimes example follows the exact same modular structure as the Goldbach example:

| Module | TwinPrimes | Goldbach | Purpose |
|--------|------------|----------|---------|
| **Spec** | `Twin p`, modal variants | `Goldbach n`, modal variants | Mathematical definitions |
| **Extract** | `find_twin_upto`, soundness | `extract_goldbach`, soundness | Witness computation |
| **Verify** | `verify_twin`, certificates | `verify_goldbach`, certificates | Verification framework |
| **Scan** | `scan_twin`, CSV logging | `scan_goldbach`, CSV logging | Counting and analysis |

This parallel structure enables:
- **Consistent API**: Same usage patterns across mathematical examples
- **Shared infrastructure**: Common verification and logging frameworks  
- **Cross-domain analysis**: Compare twin primes vs Goldbach statistics
- **Template expansion**: Easy addition of new number-theoretic examples

The twin primes conjecture (infinitely many twin primes) complements the Goldbach conjecture verification, providing ArithmoPraxis with comprehensive elementary number theory coverage.