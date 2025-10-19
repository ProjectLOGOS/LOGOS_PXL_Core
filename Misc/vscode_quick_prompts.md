# Quick Reference: High-Impact VS Code Prompts

**Context:** LOGOS_PXL_Core development - immediate productivity boosters

---

## 🚀 **Daily Development Workflows**

### Fix Admitted Proofs (High Priority)
```text
Complete this Admitted proof constructively. No axioms. 
Trinity constraint: BOX(Good ∧ TrueP ∧ Coherent).
Show proof obligations step-by-step.
```

### Replace Worker Stubs (Critical Path)
```text
Replace this stub with real implementation.
Input: RabbitMQ message with proof_token
Output: Actual reasoning result + provenance
Context: TELOS/TETRAGNOS/THONOC worker in services/workers/
```

### Eliminate SerAPI Fallbacks (Security Critical)
```text
Remove pattern-matching fallback, use only SerAPI.
Fail closed if proof verification unavailable.
Current: serve_pxl.py lines 220-250
```

### Optimize for Performance SLO (Production Blocker)
```text
Reduce latency to P95 < 300ms.
Consider: connection pooling, async, caching.
Current bottleneck: SerAPI subprocess startup.
Profile and measure improvements.
```

---

## 🎯 **Context-Aware Shortcuts**

### When editing `.v` files:
```text
Extend this Coq module maintaining constructive proofs.
No Admitted/Axiom statements.
Compatible with PXL frame system.
```

### When editing `serve_pxl.py`:
```text
Enhance SerAPI reliability and eliminate fallback patterns.
Maintain fail-closed security model.
Add structured logging for audit trail.
```

### When editing worker services:
```text
Implement real AGI capability replacing mock responses.
Validate proof_token before execution.
Return structured results with provenance.
```

### When editing gateway/API:
```text
Add production security: HMAC auth, rate limiting.
Maintain proof-gating for all state changes.
Include comprehensive error handling.
```

---

## 🔧 **Repository Navigation Prompts**

### Four-Root Structure Navigation:
```text
Generate code respecting four-root structure:
- PXL_IEL_overlay_system/ (verification)
- LOGOS_AGI/ (runtime)  
- Three_Pillars_Corpus_Literature/ (corpus)
- Misc/ (tooling)
```

### ArithmoPraxis Module Work:
```text
Extend ArithmoPraxis v0.4 in PXL_IEL_overlay_system/modules/infra/arithmo/
Follow pattern: Core/, Examples/, {Domain}/
Include constructive proofs and README.
```

---

## 🛡️ **Security & Compliance Patterns**

```text
# Audit for proof-gating compliance:
Every state mutation needs ReferenceMonitor.require_proof_token().
Log all decisions to audit/decisions.jsonl.
Fail closed on verification errors.

# Trinity validation pattern:
obligation = f"BOX(Good({action}) and TrueP({props}) and Coherent({state}))"
proof_token = reference_monitor.require_proof_token(obligation, provenance)
```

---

## ⚡ **Quick Fixes & Debugging**

### Find TODOs and Stubs:
```text
Locate TODO/stub implementations in this file.
Prioritize by impact on production readiness.
Suggest specific implementation approach.
```

### Performance Bottleneck Analysis:
```text
Profile this function for performance issues.
Identify SerAPI calls, I/O operations, algorithmic complexity.
Suggest optimizations for P95 < 300ms target.
```

### Integration Testing:
```text
Write end-to-end test for this workflow.
Include proof validation at each stage.
Mock external dependencies appropriately.
```

---

**Usage:** Copy prompt + select relevant code → Chat/Copilot → Review output → Test changes
