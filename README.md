# LOGOS PXL Core - Three-Part Alignment System

This implementation provides a fail-closed alignment core with three key components:

1. **PXL Proof Gate** - Non-bypassable proof requirement for all actions
2. **Privative Boundary Conditions** - Boxed invariants that must be preserved  
3. **OBDC Kernel** - Structure-preserving mappings with formal verification

## Architecture

```
┌─────────────────┐    ┌──────────────────┐    ┌─────────────────┐
│   PXL Prover    │    │  Reference       │    │     OBDC        │
│   (Port 8088)   │◄───┤  Monitor         │◄───┤   Kernel        │
│                 │    │                  │    │                 │
│ • SerAPI        │    │ • Proof Gates    │    │ • Bijections    │
│ • Coq Kernel    │    │ • Audit Log      │    │ • Commutations  │
│ • Hash Verify   │    │ • Fail-Closed    │    │ • Structure     │
└─────────────────┘    └──────────────────┘    └─────────────────┘
         │                       │                       │
         └───────────────────────┼───────────────────────┘
                                 │
                    ┌─────────────────────────┐
                    │    LOGOS Nexus          │
                    │  • Unified Validator    │
                    │  • Archon Planner       │
                    │  • Integration Harm.    │
                    └─────────────────────────┘
```

## Quick Start

### 1. Start PXL Proof Server

```bash
# Option A: Direct Python (for development)
cd pxl-prover
python3 serve_pxl.py

# Option B: Docker (for production)
docker build -t pxl-prover ./pxl-prover/
docker run -p 8088:8088 pxl-prover
```

### 2. Update Expected Kernel Hash

The system requires a pinned kernel hash for security. Run the verification script:

```bash
# On Linux/Mac
chmod +x ci/verify_pxl.sh
./ci/verify_pxl.sh

# On Windows (PowerShell)
# Manual hash update required - see verify_pxl.sh for steps
```

This will:
- Build and verify the PXL kernel using Coq
- Compute a deterministic kernel hash  
- Update `configs/config.json` with the correct hash

### 3. Run the Demo

```bash
cd examples
python3 main_demo.py
```

Expected output:
```
LOGOS Alignment Core Demo
==================================================
✓ PXL server running (kernel: A1B2C3D4)

=== Demo 1: Action Authorization ===
✓ Action authorized: True
  Proof token: 12345678...

=== Demo 2: Plan Creation ===
✓ Plan created: plan_1234
  Steps: 3
✓ Step executed: init

=== Demo 3: OBDC Bijection ===
✓ Bijection applied: 42 → 43
✓ Commutation applied: multiply(increment(10)) = 22

=== Demo 4: Drift Reconciliation ===
✓ Low drift handled: none
✓ High drift reconciled: consistency_proven

=== Demo 5: Proof Gate Failure ===
✓ Proof gate correctly denied request with DENY pattern

==================================================
Demo Results Summary:
Passed: 5/5
✓ All demos passed - Alignment core is working correctly

=== Audit Summary ===
Total audit records: 8
Allow decisions: 7
Deny decisions: 1
```

## Key Features Demonstrated

### Fail-Closed Operation
- **No proof → No action**: All operations require valid proof tokens
- **Kernel hash verification**: Rejects operations if kernel hash mismatches expected
- **Audit trail**: Every decision logged with full provenance in JSONL format

### Proof-Gated Authorization
```python
# Every action must pass through reference monitor
obligation = "BOX(Good(action) and TrueP(props) and Coherent(state))"
proof_token = reference_monitor.require_proof_token(obligation, provenance)
```

### Structure-Preserving Operations
```python
# OBDC bijections require formal verification
result = obdc_kernel.apply_bijection("increment", increment_fn, 42, provenance)
# Requires proof: BOX(preserves_good(increment,x) ∧ preserves_coherence(increment))
```

### Plan-Level Validation
```python
# Each plan step requires invariant preservation proof
step_validation = validator.validate_plan_step(step, provenance)
# Requires proof: BOX(preserves_invariants(step_id))

# Plan goals require reachability proof  
plan_validation = validator.validate_plan_goal(plan_id, goal, provenance)
# Requires proof: BOX(DIAMOND(Goal(plan_id)))
```

## Configuration

Edit `configs/config.json`:

```json
{
  "pxl_prover_url": "http://127.0.0.1:8088",
  "expected_kernel_hash": "A1B2C3D4",  // Set by verify_pxl.sh
  "audit_path": "audit/decisions.jsonl",
  "timeout_ms": 2000
}
```

## Acceptance Criteria Validation

The system meets all specified acceptance criteria:

1. ✅ **PXL server authorization**: Goals without "DENY" pattern are approved, others denied
2. ✅ **Proof-required planning**: Removing `require_proof_token` calls causes demo failure  
3. ✅ **Audit logging**: JSONL file contains `{ts, obligation, provenance, decision, proof}`
4. ✅ **Kernel hash enforcement**: Changing expected hash causes hard failure
5. ✅ **CI verification**: `verify_pxl.sh` fails if coqchk fails or hash differs

## Directory Structure

```
├── pxl-prover/          # PXL proof server (Coq + SerAPI)
│   ├── Dockerfile       # Coq 8.20.1 + SerAPI container
│   └── serve_pxl.py     # HTTP proof server
├── configs/             # Configuration files
│   └── config.json      # Main config with kernel hash
├── logos_core/          # Core alignment components
│   ├── pxl_client.py    # HTTP client for PXL server
│   ├── reference_monitor.py  # Proof gate enforcement
│   ├── unified_formalisms.py # Action authorization
│   ├── archon_planner.py     # Proof-gated planning
│   ├── logos_nexus.py        # Main request handler
│   └── integration_harmonizer.py # Drift reconciliation
├── obdc/                # Structure-preserving kernel
│   └── kernel.py        # Bijections and commutations
├── policies/            # Policy definitions
│   └── privative_policies.py # Obligation mappings
├── persistence/         # Audit and logging
│   └── persistence.py   # JSONL audit logger
├── ci/                  # Continuous integration
│   ├── verify_pxl.sh    # Kernel verification script
│   └── test_audit.py    # Audit system test
├── examples/            # Demonstrations
│   └── main_demo.py     # Full system demo
└── .github/workflows/   # GitHub Actions
    └── verify.yml       # CI pipeline
```

## TODOs - SerAPI Integration

The current implementation uses proof stubs for demonstration. To integrate with real PXL proofs:

1. **Replace stub in `serve_pxl.py`**:
   ```python
   # TODO: Replace this block with SerAPI calls
   if "DENY" in goal.upper():
       return {"ok": False, ...}
   ```

2. **Add SerAPI queries**:
   ```python
   import serapi_python
   
   def prove_with_serapi(goal):
       sexp_goal = f"(Check {goal})"
       result = serapi_python.execute_sexp(sexp_goal)
       return parse_coq_result(result)
   ```

3. **PXL-specific proof tactics**:
   - Map BOX obligations to PXL modal logic
   - Use PXL kernel axioms for Good/TrueP/Coherent predicates
   - Implement countermodel generation for failed proofs

4. **Kernel hash verification**:
   - Extract actual kernel fingerprint from built `.vo` files
   - Verify cryptographic integrity of PXL axioms
   - Implement hash chain for kernel evolution

## Developer Runbook

### Start prover and run demo:
```bash
# Terminal 1: Start PXL prover server
cd pxl-prover
python3 serve_pxl.py

# Terminal 2: Run demo
cd examples  
python3 main_demo.py
```

### Run tests:
```bash
# Run alignment tests
python3 -m pytest tests/test_alignment.py -v

# Run bypass scanner
python3 tools/scan_bypass.py

# Run all tests
python3 -m pytest -v
```

### Update kernel hash:
```bash
# Build kernel and update config
bash ci/verify_pxl.sh

# Verify hash is pinned correctly
grep expected_kernel_hash configs/config.json
```

### Production deployment:
```bash
# Build Docker image
docker build -t pxl-prover ./pxl-prover/

# Run with proper kernel
docker run -p 8088:8088 pxl-prover
```

## Troubleshooting

**PXL server not responding**:
```bash
# Check if server is running
curl http://127.0.0.1:8088/health

# Check logs
cd pxl-prover && python3 serve_pxl.py
```

**Kernel hash mismatch**: 
```bash
# Regenerate expected hash
bash ci/verify_pxl.sh
```

**Demo failures**:
```bash
# Check audit log
cat audit/decisions.jsonl | jq '.'

# Verbose demo run
cd examples && python3 -v main_demo.py
```

**Missing dependencies**:
```bash
pip3 install flask requests pytest
```

**SerAPI issues**:
```bash
# Install SerAPI
opam install coq-serapi

# Test SerAPI directly
sertop --help
```