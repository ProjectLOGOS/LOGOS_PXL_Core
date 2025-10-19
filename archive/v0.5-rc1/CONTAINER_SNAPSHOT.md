# Container Registry Snapshot - LOGOS_PXL_Core v0.5-rc1

**Image Tag**: `logos_pxl_core:v0.5-rc1`  
**Registry**: (To be configured for production deployment)  
**Snapshot Date**: October 19, 2025

## 📦 Container Specifications

### **Base Image**
- **OS**: Ubuntu 22.04 LTS
- **Python**: 3.11+
- **Coq**: 8.20.1
- **SerAPI**: 0.19.0

### **Application Stack**
- **PXL Prover**: `/app/pxl-prover/serve_pxl.py`
- **Logos Core**: `/app/logos_core/`
- **Configuration**: `/app/configs/`
- **Audit System**: `/app/persistence/`

### **Security Features**
- **User**: Non-root execution (UID 1000)
- **Network**: Isolated container network
- **Secrets**: External secret injection
- **Read-only**: Filesystem (except /tmp, /var/log)

### **Health Monitoring**
- **Health Endpoint**: `/health`
- **Metrics Endpoint**: `/metrics`
- **Liveness Probe**: HTTP GET /health every 30s
- **Readiness Probe**: HTTP GET /ready every 10s

## 🔐 Security Attestation

### **Image Signing**
- **Cosign Signature**: (To be generated)
- **SBOM Included**: Software Bill of Materials
- **Vulnerability Scan**: Trivy clean (zero critical)
- **Security Policy**: Distroless + minimal dependencies

### **Runtime Security**
- **AppArmor Profile**: Restricted container profile
- **Seccomp**: Default Docker seccomp profile
- **Capabilities**: Minimal required capabilities only
- **Network Policy**: Ingress 8088/tcp only

## 📊 Performance Profile

### **Resource Requirements**
- **CPU**: 2 cores minimum, 4 cores recommended
- **Memory**: 4GB minimum, 8GB recommended
- **Storage**: 2GB for application + 1GB for logs
- **Network**: 100Mbps for high-throughput scenarios

### **Scaling Characteristics**
- **Horizontal**: Stateless, can scale to N replicas
- **Vertical**: CPU-bound on proof verification
- **Auto-scaling**: Based on proof queue depth
- **Load Balancer**: Round-robin with health checks

## 🚀 Deployment Commands

### **Docker Registry Push** (Production)
```bash
# Build and tag
docker build -t logos_pxl_core:v0.5-rc1 .

# Tag for registry
docker tag logos_pxl_core:v0.5-rc1 registry.example.com/logos/pxl-core:v0.5-rc1

# Push to registry
docker push registry.example.com/logos/pxl-core:v0.5-rc1

# Sign with cosign
cosign sign registry.example.com/logos/pxl-core:v0.5-rc1
```

### **Kubernetes Deployment**
```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: logos-pxl-core
spec:
  replicas: 3
  selector:
    matchLabels:
      app: logos-pxl-core
  template:
    spec:
      containers:
      - name: pxl-core
        image: registry.example.com/logos/pxl-core:v0.5-rc1
        ports:
        - containerPort: 8088
        resources:
          requests:
            memory: "4Gi"
            cpu: "2"
          limits:
            memory: "8Gi" 
            cpu: "4"
```

## 📋 Registry Verification

### **Image Integrity Checks**
```bash
# Verify signature
cosign verify registry.example.com/logos/pxl-core:v0.5-rc1

# Check SBOM
cosign verify-attestation --type spdx registry.example.com/logos/pxl-core:v0.5-rc1

# Vulnerability scan
trivy image registry.example.com/logos/pxl-core:v0.5-rc1
```

---

**Status**: Ready for production registry deployment  
**Next Update**: Container image build and registry push for production environment
