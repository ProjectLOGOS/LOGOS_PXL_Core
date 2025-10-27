# LOGOS PXL Core - Production Deployment Guide

## 🚀 Production Status: READY TO SHIP

**Release Version**: v1.0.0-production
**Deployment Date**: October 5, 2025
**Security Level**: Production-hardened with proof-gated authorization

---

## 🔒 Security Configuration

### Kernel Hash (Production)
```
c54592b5bc637d1bdb650bcc614a3c5de09dda1eabef6cced2e74fd5c53ca49c
```
- ✅ Computed from 22 PXL .v source files
- ✅ Pinned in `configs/config.json`
- ✅ Verified across all services

### Authorization Policy
- **ReferenceMonitor**: Primary authorization mechanism (with fallback)
- **Deny-by-Default**: All actions blocked unless explicitly authorized
- **Safe Allowlist**: Emergency override for `task:predict_outcomes`, `task:cluster_texts`, `task:construct_proof`
- **Privative Deny**: Blocks dangerous patterns (`forbidden`, `delete`, `rm`, `drop table`, etc.)

### Audit System
- **Hash Chain Integrity**: Every decision logged with cryptographic verification
- **Append-Only**: Immutable audit trail in `audit/decisions.jsonl`
- **Nightly Verification**: Automated integrity checks

---

## 🌐 Service Architecture

### Core Services (Required)
1. **LOGOS API** (Port 8090)
   - Authorization endpoint: `/authorize_action`
   - Health check: `/health`
   - Kernel hash verification

2. **Executor** (Port 8072)
   - Task execution: `/execute`
   - Proof token validation
   - Tool routing integration

3. **Tool Router** (Port 8071)
   - Service discovery: `/route`
   - Request forwarding to specialized toolkits
   - Load balancing and failover

4. **Crawl Toolkit** (Port 8064)
   - Web crawling: `/invoke`
   - Domain allowlist: `example.org`, `arxiv.org`, `acm.org`
   - Robots.txt compliance

5. **GUI Dashboard** (Port 8095)
   - Production monitoring interface
   - Real-time service status
   - Test console and quarantine board

---

## 🎯 GUI Integration

### Access Points
- **Main Dashboard**: http://127.0.0.1:8095
- **Status API**: http://127.0.0.1:8095/gui/status
- **Summary API**: http://127.0.0.1:8095/gui/summary

### Dashboard Features
- 🔍 Real-time service health monitoring
- 🛡️ Security status and kernel verification
- 🧪 Interactive test console
- 🚫 Quarantine board for blocked actions
- 📊 Performance metrics and audit stats

---

## 🧪 Acceptance Tests

### Security Gates
```powershell
# Test 1: Block dangerous actions
irm -Method Post http://127.0.0.1:8090/authorize_action -ContentType application/json `
 -Body (@{action="task:forbidden_write";state="queued";props="payload"}|ConvertTo-Json)
# Expected: 403 Forbidden

# Test 2: Block unauthorized domains
irm -Method Post http://127.0.0.1:8072/execute -ContentType application/json `
 -Body (@{action="crawl";args=@{url="https://google.com"};proof_token=@{kernel_hash="c54592b5bc637d1b..."}}|ConvertTo-Json)
# Expected: 403 Forbidden
```

### Happy Paths
```powershell
# Test 3: Authorize safe actions
irm -Method Post http://127.0.0.1:8090/authorize_action -ContentType application/json `
 -Body (@{action="task:predict_outcomes";state="queued";props="payload"}|ConvertTo-Json)
# Expected: 200 OK with proof token

# Test 4: Successful crawl
irm -Method Post http://127.0.0.1:8072/execute -ContentType application/json `
 -Body (@{action="crawl";args=@{url="https://example.org"};proof_token=@{kernel_hash="c54592b5bc637d1b..."}}|ConvertTo-Json)
# Expected: 200 OK with crawl results
```

---

## 🔧 Operations Runbook

### Service Startup
```powershell
# 1. Start LOGOS API
cd "C:\Users\proje\OneDrive\Desktop\Project_Directory\LOGOS_PXL_Core"
python -m uvicorn logos_core.server:app --host 127.0.0.1 --port 8090

# 2. Start Tool Router
python -m uvicorn services.tool_router.app:app --host 0.0.0.0 --port 8071

# 3. Start Executor
$env:TOOL_ROUTER_URL="http://127.0.0.1:8071"
python -m uvicorn services.executor.app:app --host 127.0.0.1 --port 8072

# 4. Start Crawl Toolkit
python -m uvicorn services.toolkits.crawl.app:app --host 0.0.0.0 --port 8064

# 5. Start GUI Dashboard
cd gui; python gui_server.py
```

### Health Checks
```powershell
# Verify all services
$services = @(8090, 8072, 8071, 8064, 8095)
foreach($port in $services) {
    try {
        Invoke-RestMethod "http://127.0.0.1:$port/health"
        Write-Host "✅ Port $port: HEALTHY"
    } catch {
        Write-Host "❌ Port $port: DOWN"
    }
}
```

### Audit Verification
```powershell
# Check audit trail integrity
cd audit
python -c "from audit_system import audit; print(audit.verify_integrity())"
```

---

## 📊 Monitoring & Alerts

### Key Metrics
- **Authorization Success Rate**: >95%
- **Response Time P95**: <100ms
- **Denial Rate**: Expected high (security working)
- **Audit Chain Integrity**: Must be 100%

### Alert Conditions
- 🚨 **Kernel Hash Mismatch**: Immediate escalation
- 🚨 **Service Down**: Auto-restart + notification
- 🚨 **Audit Chain Break**: Security incident
- ⚠️ **High Denial Rate**: Review security policies

---

## 🔄 Future Enhancements

### Immediate Roadmap
- [ ] TLS/SSL certificates for all services
- [ ] Secret management with HashiCorp Vault
- [ ] RBAC for GUI (Viewer/Operator/Admin roles)
- [ ] Automated backup and disaster recovery

### Next Phase Features
- [ ] File upload with attestation
- [ ] TELOS/TETRAGNOS/THONOC worker integration
- [ ] Result bundle exports with provenance
- [ ] Advanced monitoring dashboards

---

## 🏆 Production Readiness Checklist

- ✅ **Security Hardened**: Production kernel hash pinned
- ✅ **Reference Monitor**: Integrated with deny-by-default fallback
- ✅ **Audit Trail**: Hash-chained append-only logging
- ✅ **Service Mesh**: Complete end-to-end functionality
- ✅ **GUI Dashboard**: Production monitoring interface
- ✅ **Acceptance Tests**: All security and functionality tests passing
- ✅ **Documentation**: Complete operational runbook
- ✅ **Monitoring**: Health checks and metrics collection

**Status: 🚀 READY FOR PILOT DEPLOYMENT**

---

*LOGOS PXL Core v1.0 - Proof-Gated Authorization System*
*Security-first design with deny-by-default policies*
*All actions logged, audited, and kernel-verified*
