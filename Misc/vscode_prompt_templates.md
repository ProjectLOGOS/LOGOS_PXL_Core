# VS Code Prompt Templates for LOGOS_PXL_Core Development

**Version:** v0.4.2-recovery  
**Context:** Integrated assistant workflows (GitHub Copilot, OpenAI, etc.)  
**Repository:** LOGOS_PXL_Core - Trinity-grounded formal AGI system  

---

## 🧩 1. **Formal Verification Prompts (Coq / SerAPI Work)**

### A. Complete Admitted Proofs
```text
# Prompt:
You are completing an unfinished Coq proof marked "Admitted" in PXL_Core.
Use only constructive tactics (no classical axioms). Ensure the lemma aligns with the Trinity-Coherence invariant:
∀s, BOX(Good(s) ∧ TrueP(s) ∧ Coherent(s)).
Explain reasoning in comments.
```

### B. Generate Proof Templates
```text
# Prompt:
Generate a Coq proof skeleton for a new lemma:
Lemma {NAME} : {SPEC}.
Constraints:
1. No axioms.
2. Compatible with PXL_Core frame system.
3. Use dependent types for context binding.
4. Include comments summarizing proof obligations.
```

### C. Debug SerAPI Queries
```text
# Prompt:
Analyze this SerAPI query output and suggest why it fails.
Show possible Coq syntax or type mismatches, and rewrite the corrected command.
Context: serve_pxl.py uses SerAPI for proof verification with fallback patterns.
```

### D. Modal Logic Frame Properties
```text
# Prompt:
Extend this ModalPraxis frame property definition with constructive proofs.
Target: Parameterized frame properties for S4/S5 modal systems.
Constraint: Must integrate with existing PXL canonical model construction.
Reference: PXL_IEL_overlay_system/modules/IEL/infra/ModalPraxis/
```

---

## ⚙️ 2. **Python Runtime Development (LOGOS_AGI / PXL Server)**

### A. Strengthen Proof-Gating
```text
# Prompt:
Audit this Python function for proof-gating compliance.
Add a verification call using the PXL proof API before any state mutation.
Raise ProofValidationError if BOX(Good ∧ TrueP ∧ Coherent) fails.
Context: All operations must go through ReferenceMonitor.require_proof_token()
```

### B. Implement Goal Lifecycle
```text
# Prompt:
Implement a goal lifecycle handler with the following states:
['created', 'verified', 'decomposed', 'executing', 'completed', 'failed'].
Integrate proof-check at transition to 'executing'.
Context: Integrate with ArchonNexus workflow architecture and UnifiedFormalismValidator.
```

### C. Fault-Tolerant SerAPI Session
```text
# Prompt:
Write a Python class managing a persistent SerAPI subprocess.
Features:
- Automatic reconnect
- Proof cache (hash: result)
- Timeout handling
- Structured JSON response
Context: Enhance serve_pxl.py reliability, eliminate fallback pattern matching.
```

### D. Fix SerAPI Integration
```text
# Prompt:
Replace pattern-matching fallbacks in serve_pxl.py with robust SerAPI calls.
Ensure every proof request goes through actual Coq verification.
Handle SerAPI failures gracefully without compromising security (fail-closed).
Current issue: Falls back to keyword matching when SerAPI unavailable.
```

---

## 🧠 3. **Cognitive and AGI Layer (TELOS / TETRAGNOS / THONOC)**

### A. Integrate Causal Reasoning (TELOS)
```text
# Prompt:
Extend TELOS module with a Bayesian causal reasoning loop.
Input: observation stream
Output: causal graph update
Constraint: Every update must log a proof verification ID.
Context: Replace stub implementation in PXL_IEL_overlay_system/services/workers/telos/
```

### B. Semantic Interface (TETRAGNOS)
```text
# Prompt:
Write a parser that converts natural-language goals into logical predicates
compatible with PXL proof schemas. Use regex + symbolic mapping table.
Context: Integrate with TETRAGNOS NLP capabilities, output BOX() formulas.
```

### C. Coherence Metric Implementation (THONOC)
```text
# Prompt:
Implement a coherence metric function that computes Φ as
Φ = 1 - (entropy(state) / entropy(reference)).
Return numerical coherence index for runtime feedback loop.
Context: THONOC logical reasoning worker, integrate with consistency_check toolkit.
```

### D. Replace Worker Stubs
```text
# Prompt:
Replace this worker stub with actual implementation.
Requirements:
- Consume from RabbitMQ task queue
- Validate input with proof token
- Execute real reasoning algorithm  
- Publish results with provenance
Context: Current workers are placeholder implementations returning mock data.
```

---

## 🧱 4. **Infrastructure / CI / Deployment**

### A. Proof-Build Integration
```text
# Prompt:
Write a CI script to compile all Coq `.v` files.
Fail pipeline if any 'Admitted' remains.
Generate a coverage report showing verified vs. unverified modules.
Context: Integrate with existing build.ps1 and .github/workflows/coq.yml
```

### B. API Security Hardening
```text
# Prompt:
Add HMAC-based authentication to FastAPI endpoints.
Each incoming request must validate a timestamped signature header.
Context: Enhance existing gateway/gateway.py with production security.
```

### C. Monitoring and Logging
```text
# Prompt:
Add structured JSON logging to all microservices.
Include: timestamp, service_name, proof_id, goal_id, result_status.
Context: Integrate with existing audit system (audit/decisions.jsonl format).
```

### D. Performance Optimization
```text
# Prompt:
Optimize this component for P95 < 300ms latency target.
Consider: connection pooling, caching, async operations, batch processing.
Current bottleneck: SerAPI process startup and proof verification time.
Context: Production SLO requirements from DEPLOYMENT.md
```

---

## 🔧 5. **Repository-Specific Workflows**

### A. Four-Root Directory Navigation
```text
# Prompt:
Generate file operations respecting the four-root structure:
- Three_Pillars_Corpus_Literature/ (canonical corpus)
- PXL_IEL_overlay_system/ (verification suite) 
- LOGOS_AGI/ (AGI runtime)
- Misc/ (tooling and infrastructure)
Context: Repository restructured in v0.4.2-recovery, update all path references.
```

### B. IEL Module Integration  
```text
# Prompt:
Create a new IEL (Internal Emergent Logic) module following the pattern:
PXL_IEL_overlay_system/modules/IEL/pillars/{ModuleName}/
Include: modal/, theorems/, systems/, docs/ subdirectories.
Constraint: Zero axiom admits, constructive proofs only.
```

### C. ArithmoPraxis Extension
```text
# Prompt:
Extend the ArithmoPraxis v0.4 module with new mathematical domain.
Location: PXL_IEL_overlay_system/modules/infra/arithmo/
Pattern: Follow existing structure (Core/, Examples/, NumberTheory/, etc.)
Include: .v files, README.md, TODO checklist.
```

---

## 📊 6. **Production Readiness & Operations**

### A. SLO Monitoring Implementation
```text
# Prompt:
Implement SLO tracking for:
- P95 latency < 300ms
- Error rate < 5%  
- Uptime > 99.9%
Export metrics to Prometheus format for Grafana dashboards.
Context: Production deployment requirements from PRODUCTION_DEPLOYMENT_CHECKLIST.md
```

### B. Health Check Enhancement
```text
# Prompt:
Enhance service health checks to include:
- SerAPI process status
- Kernel hash verification
- Proof queue depth
- Memory/CPU utilization
Return structured JSON with detailed diagnostic info.
```

### C. Deployment Automation
```text
# Prompt:
Create deployment script following blue/green pattern.
Validate kernel hash consistency across deployments.
Include rollback capability and health verification.
Context: Use existing docker-compose.prod.yml as foundation.
```

---

## 🔬 7. **Research & Development Extensions**

### A. Self-Modification Safeguards
```text
# Prompt:
Design a sandbox environment where THONOC can propose a code patch.
All patches must pass:
1. Proof re-verification  
2. Static safety checks
3. Semantic diff approval
Return approved patch set only.
Context: Integrate with GodelianDesireDriver and SelfImprovementManager concepts.
```

### B. Cross-Modal Reasoning
```text
# Prompt:
Implement integration between multiple IEL modules (ChronoPraxis, ModalPraxis, etc.).
Ensure modal operators compose correctly across temporal and ontological domains.
Maintain constructive proof requirements throughout.
```

### C. Trinity Validation Deep Dive
```text
# Prompt:
Implement deeper Trinity principle validation in UnifiedFormalismValidator.
Check not just BOX(Good ∧ TrueP ∧ Coherent) but also:
- Necessity (modal S5 properties)
- Reason (logical consistency)  
- Generativity (creative expansion within bounds)
```

---

## 🧰 8. **Debugging & Analysis Prompts**

### A. Proof Coverage Analysis
```text
# Prompt:
Write a Python script scanning all `.v` files for 'Admitted' keywords.
Output: verified_count, total_count, verification_ratio.
Generate report showing which modules need completion.
Context: Target is zero admits for production readiness.
```

### B. Performance Profiling
```text
# Prompt:
Add performance profiling to this function.
Measure: execution time, memory usage, SerAPI round-trips.
Log results in JSON format compatible with audit system.
Identify optimization opportunities for P95 < 300ms target.
```

### C. Integration Testing
```text
# Prompt:
Write comprehensive integration test for this workflow:
Goal → ArchonNexus → WorkflowArchitect → Worker → Result
Include proof validation at each stage.
Mock external dependencies, validate message flows.
```

---

## 🎯 9. **Specialized Domain Prompts**

### A. Philosophical Consistency  
```text
# Prompt:
Ensure this implementation aligns with Three Pillars of Divine Necessity:
1. Ontological grounding (what exists)
2. Epistemological validation (what can be known)  
3. Axiological coherence (what is good/valuable)
Reference Trinity principles in code comments.
```

### B. Mathematical Rigor
```text
# Prompt:
Convert this algorithm into constructive mathematical form.
Use dependent types where appropriate.
Prove termination and correctness properties.
No classical logic axioms - constructive proofs only.
```

### C. Security Model Validation
```text
# Prompt:
Audit this component against the privative security model:
- No action without proof token
- Fail-closed on verification failure
- Complete audit trail logging
- Kernel hash integrity verification
Reference: policies/privative_policies.py patterns
```

---

## ✅ **Enhanced Usage Guidelines**

### IDE Integration Tips:
* **File Context**: Keep relevant `.v`, `.py`, and `.md` files open for better completions
* **Selection Scope**: Select specific functions/lemmas for targeted assistance  
* **Multi-file Reasoning**: Use chat window for cross-file architectural questions
* **Build Integration**: Run `build.ps1` before major prompt sessions to ensure context freshness

### Prompt Customization:
```text
# Template Variables:
{NAME} - Replace with actual identifier
{SPEC} - Replace with type specification  
{CONTEXT} - Add specific file/module context
{CONSTRAINT} - Add domain-specific requirements
```

### Quality Assurance:
* Always test generated Coq proofs with `coqc`
* Run `verify_pxl.sh` after formal verification changes
* Execute relevant test suites after Python modifications
* Check pre-commit hooks before committing changes

### Context Management:
```text
# Include in prompts when relevant:
Repository Structure: Four-root directory layout
Version: v0.4.2-recovery  
Architecture: Microservices + SerAPI + RabbitMQ
Security Model: Proof-gated authorization
Performance Target: P95 < 300ms, Error rate < 5%
```

---

**Generated by LOGOS_PXL_Core Development Framework**  
*Last Updated: 2025-10-19*  
*Kernel Hash: [Current kernel hash from verify_pxl.sh]*
