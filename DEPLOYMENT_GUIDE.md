# LOGOS_PXL_Core v0.5 - Production Deployment Guide

**Version**: v0.5-rc1  
**Last Updated**: October 19, 2025  
**Target Environment**: Production-Ready Verified AGI System

---

## 🎯 **Overview**

This guide provides comprehensive instructions for deploying LOGOS_PXL_Core v0.5 in production environments. The system achieves **94%+ verification ratio** with **sub-300ms P95 latency** and production-grade security hardening.

---

## 📋 **Prerequisites**

### **System Requirements**
- **OS**: Linux (Ubuntu 20.04+ recommended), macOS, or Windows with WSL2
- **CPU**: 4+ cores (8+ recommended for high throughput)
- **Memory**: 8GB RAM minimum (16GB+ recommended)
- **Storage**: 10GB available space
- **Network**: Stable internet for dependency installation

### **Software Dependencies**
- **Python**: 3.8+ (3.11+ recommended)
- **Coq**: 8.15+ with SerAPI support
- **Docker**: 20.10+ (for containerized deployment)
- **Git**: For version control and updates

### **Required Python Packages**
```bash
pip install flask waitress requests hashlib threading
```

---

## 🚀 **Deployment Methods**

## **Method 1: Direct Python Deployment (Recommended for Development)**

### **Step 1: Repository Setup**
```bash
# Clone repository
git clone https://github.com/ProjectLOGOS/LOGOS_PXL_Core.git
cd LOGOS_PXL_Core

# Checkout production release
git checkout v0.5-rc1

# Install dependencies
pip install -r requirements.txt
```

### **Step 2: Environment Configuration**
```bash
# Set environment variables
export ENABLE_HMAC_AUTH=true
export HMAC_SECRET_KEY="your-secure-256-bit-key-here"
export PXL_SERVER_PORT=8088
export PXL_POOL_SIZE=5
export PXL_CACHE_TTL=300
```

### **Step 3: Start PXL Proof Server**
```bash
cd PXL_IEL_overlay_system/pxl-prover
python serve_pxl.py
```

**Expected Output:**
```
INFO:performance:Performance monitor initialized
PXL Kernel Hash: 592d2b2afc46fb236b0354853305e33a81e897686df2f1bb3e2f254735d67edc
Starting OPTIMIZED PXL Proof Server with kernel hash: 592d2b2...
Session pool size: 5
Cache TTL: 300s
HMAC Authentication: Enabled
Using Waitress WSGI server for production stability...
INFO:waitress:Serving on http://0.0.0.0:8088
```

### **Step 4: Validation**
```bash
# Health check
curl http://localhost:8088/health

# Metrics endpoint
curl http://localhost:8088/metrics

# Sample proof request (with HMAC if enabled)
curl -X POST http://localhost:8088/prove \
  -H "Content-Type: application/json" \
  -d '{"goal": "BOX(A -> A)"}'
```

---

## **Method 2: Docker Deployment (Recommended for Production)**

### **Step 1: Build Docker Image**
```bash
# Build production image
docker build -t logos-pxl-core:v0.5-rc1 -f Dockerfile.pxl-core .

# Verify image
docker images | grep logos-pxl-core
```

### **Step 2: Docker Compose Deployment**
Create `docker-compose.prod.yml`:

```yaml
version: '3.8'

services:
  pxl-prover:
    image: logos-pxl-core:v0.5-rc1
    ports:
      - "8088:8088"
    environment:
      - ENABLE_HMAC_AUTH=true
      - HMAC_SECRET_KEY=${HMAC_SECRET_KEY}
      - PXL_SERVER_PORT=8088
      - PXL_POOL_SIZE=10
      - PXL_CACHE_TTL=600
    volumes:
      - ./logs:/app/logs
      - ./configs:/app/configs
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8088/health"]
      interval: 30s
      timeout: 10s
      retries: 3
      start_period: 40s

  monitoring:
    image: prom/prometheus
    ports:
      - "9090:9090"
    volumes:
      - ./monitoring/prometheus.yml:/etc/prometheus/prometheus.yml
    command:
      - '--config.file=/etc/prometheus/prometheus.yml'
      - '--storage.tsdb.path=/prometheus'
    depends_on:
      - pxl-prover

volumes:
  logs:
  configs:
```

### **Step 3: Start Production Stack**
```bash
# Set secure secret key
export HMAC_SECRET_KEY=$(openssl rand -hex 32)

# Start services
docker-compose -f docker-compose.prod.yml up -d

# Verify deployment
docker-compose -f docker-compose.prod.yml ps
```

---

## **Method 3: Kubernetes Deployment (Enterprise)**

### **Step 1: Create Namespace**
```yaml
# kubernetes/namespace.yaml
apiVersion: v1
kind: Namespace
metadata:
  name: logos-pxl-core
  labels:
    name: logos-pxl-core
    version: v0.5-rc1
```

### **Step 2: Deploy Application**
```yaml
# kubernetes/deployment.yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: pxl-prover
  namespace: logos-pxl-core
spec:
  replicas: 3
  selector:
    matchLabels:
      app: pxl-prover
  template:
    metadata:
      labels:
        app: pxl-prover
    spec:
      containers:
      - name: pxl-prover
        image: logos-pxl-core:v0.5-rc1
        ports:
        - containerPort: 8088
        env:
        - name: ENABLE_HMAC_AUTH
          value: "true"
        - name: HMAC_SECRET_KEY
          valueFrom:
            secretKeyRef:
              name: pxl-secrets
              key: hmac-secret
        - name: PXL_POOL_SIZE
          value: "10"
        resources:
          requests:
            memory: "2Gi"
            cpu: "1"
          limits:
            memory: "4Gi"
            cpu: "2"
        livenessProbe:
          httpGet:
            path: /health
            port: 8088
          initialDelaySeconds: 30
          periodSeconds: 30
        readinessProbe:
          httpGet:
            path: /health
            port: 8088
          initialDelaySeconds: 5
          periodSeconds: 5
```

### **Step 3: Service and Ingress**
```yaml
# kubernetes/service.yaml
apiVersion: v1
kind: Service
metadata:
  name: pxl-prover-service
  namespace: logos-pxl-core
spec:
  selector:
    app: pxl-prover
  ports:
  - port: 8088
    targetPort: 8088
  type: ClusterIP

---
# kubernetes/ingress.yaml
apiVersion: networking.k8s.io/v1
kind: Ingress
metadata:
  name: pxl-prover-ingress
  namespace: logos-pxl-core
  annotations:
    nginx.ingress.kubernetes.io/ssl-redirect: "true"
    nginx.ingress.kubernetes.io/rate-limit-rps: "100"
spec:
  tls:
  - hosts:
    - pxl.yourdomain.com
    secretName: pxl-tls
  rules:
  - host: pxl.yourdomain.com
    http:
      paths:
      - path: /
        pathType: Prefix
        backend:
          service:
            name: pxl-prover-service
            port:
              number: 8088
```

---

## ⚙️ **Configuration Management**

### **Environment Variables**

| Variable | Default | Description |
|----------|---------|-------------|
| `ENABLE_HMAC_AUTH` | `false` | Enable HMAC authentication |
| `HMAC_SECRET_KEY` | `None` | 256-bit secret key for HMAC |
| `PXL_SERVER_PORT` | `8088` | Server listening port |
| `PXL_POOL_SIZE` | `5` | Initial SerAPI session pool size |
| `PXL_CACHE_TTL` | `300` | Proof cache TTL in seconds |
| `LOG_LEVEL` | `INFO` | Logging level (DEBUG, INFO, WARN, ERROR) |
| `MAX_REQUEST_SIZE` | `1048576` | Maximum request body size (bytes) |
| `CONNECTION_TIMEOUT` | `60` | Connection timeout in seconds |

### **Security Configuration**

#### **HMAC Authentication Setup**
```bash
# Generate secure secret key
openssl rand -hex 32

# Set in environment
export HMAC_SECRET_KEY="your-generated-key-here"

# Enable authentication
export ENABLE_HMAC_AUTH=true
```

#### **Request Signing (Client Side)**
```python
import hmac
import hashlib
import time

def generate_hmac_headers(secret_key, body=""):
    timestamp = str(int(time.time()))
    nonce = hashlib.sha256(f"{timestamp}{time.time()}".encode()).hexdigest()[:16]
    
    signature_data = f"{timestamp}:{nonce}:{body}"
    signature = hmac.new(
        secret_key.encode('utf-8'),
        signature_data.encode('utf-8'),
        hashlib.sha256
    ).hexdigest()
    
    return {
        "X-Timestamp": timestamp,
        "X-Nonce": nonce,
        "X-Signature": signature
    }
```

### **Performance Tuning**

#### **Session Pool Optimization**
- **Low Load**: `PXL_POOL_SIZE=3-5` (default)
- **Medium Load**: `PXL_POOL_SIZE=10-15` 
- **High Load**: `PXL_POOL_SIZE=20+` with load balancing

#### **Cache Optimization**
- **Development**: `PXL_CACHE_TTL=300` (5 minutes)
- **Production**: `PXL_CACHE_TTL=600-1800` (10-30 minutes)
- **High Frequency**: Enable semantic prefetching (automatic in v0.5)

#### **Memory Management**
- **Cache Size**: Automatically managed (1000 entries max)
- **Session Cleanup**: Automatic expired session cleanup
- **Memory Monitoring**: Available via `/metrics` endpoint

---

## 📊 **Monitoring and Observability**

### **Health Endpoints**

#### **Basic Health Check**
```bash
curl http://localhost:8088/health
```

**Response:**
```json
{
  "status": "ok",
  "ready": true,
  "kernel_hash": "592d2b2afc46fb236b0354853305e33a81e897686df2f1bb3e2f254735d67edc",
  "session_pool": {
    "total_sessions": 5,
    "active_sessions": 4,
    "busy_sessions": 1,
    "max_pool_size": 5,
    "utilization_rate": 0.2
  },
  "timestamp": 1698582431
}
```

#### **Comprehensive Metrics (Prometheus-Compatible)**
```bash
curl http://localhost:8088/metrics
```

**Key Metrics:**
```json
{
  "logos_pxl_uptime_seconds": 3600,
  "logos_pxl_verification_ratio_percent": 94.7,
  "logos_pxl_p95_latency_ms": 245.8,
  "logos_pxl_cache_hit_rate_percent": 87.3,
  "logos_pxl_session_pool_total": 5,
  "logos_pxl_cache_hits_total": 1420,
  "logos_pxl_cache_misses_total": 203
}
```

### **Prometheus Integration**

#### **Prometheus Configuration** (`monitoring/prometheus.yml`)
```yaml
global:
  scrape_interval: 15s

scrape_configs:
  - job_name: 'pxl-core'
    static_configs:
      - targets: ['pxl-prover:8088']
    metrics_path: '/metrics'
    scrape_interval: 30s
```

#### **Key Alerts**
```yaml
# alerts.yml
groups:
- name: pxl-core
  rules:
  - alert: HighLatency
    expr: logos_pxl_p95_latency_ms > 300
    for: 2m
    annotations:
      summary: "PXL Core P95 latency exceeds 300ms"
      
  - alert: LowVerificationRatio
    expr: logos_pxl_verification_ratio_percent < 90
    for: 1m
    annotations:
      summary: "Verification ratio below 90%"
      
  - alert: CacheHitRateLow
    expr: logos_pxl_cache_hit_rate_percent < 70
    for: 5m
    annotations:
      summary: "Cache hit rate below 70%"
```

---

## 🔧 **Scaling and Load Balancing**

### **Horizontal Scaling**

#### **Load Balancer Configuration (Nginx)**
```nginx
upstream pxl_backend {
    least_conn;
    server pxl-1:8088 max_fails=3 fail_timeout=30s;
    server pxl-2:8088 max_fails=3 fail_timeout=30s;
    server pxl-3:8088 max_fails=3 fail_timeout=30s;
}

server {
    listen 80;
    server_name pxl.yourdomain.com;
    
    location / {
        proxy_pass http://pxl_backend;
        proxy_set_header Host $host;
        proxy_set_header X-Real-IP $remote_addr;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_connect_timeout 30s;
        proxy_send_timeout 60s;
        proxy_read_timeout 60s;
    }
    
    location /health {
        proxy_pass http://pxl_backend;
        access_log off;
    }
}
```

### **Auto-Scaling (Kubernetes)**
```yaml
apiVersion: autoscaling/v2
kind: HorizontalPodAutoscaler
metadata:
  name: pxl-prover-hpa
  namespace: logos-pxl-core
spec:
  scaleTargetRef:
    apiVersion: apps/v1
    kind: Deployment
    name: pxl-prover
  minReplicas: 3
  maxReplicas: 20
  metrics:
  - type: Resource
    resource:
      name: cpu
      target:
        type: Utilization
        averageUtilization: 70
  - type: Resource
    resource:
      name: memory
      target:
        type: Utilization
        averageUtilization: 80
```

---

## 🚨 **Disaster Recovery**

### **Backup Strategy**

#### **Configuration Backup**
```bash
# Backup critical configurations
tar -czf logos-pxl-backup-$(date +%Y%m%d).tar.gz \
  configs/ \
  logs/ \
  docker-compose.prod.yml \
  kubernetes/ \
  monitoring/
```

#### **State Recovery**
```bash
# The PXL Core is stateless - recovery involves:
# 1. Restore configuration files
# 2. Restart services
# 3. Validate health endpoints
# 4. Verify proof functionality

# Quick recovery test
curl -X POST http://localhost:8088/prove \
  -H "Content-Type: application/json" \
  -d '{"goal": "BOX(A -> A)"}'
```

### **Failover Procedures**

#### **Primary Service Failure**
1. **Detection**: Health check failure or monitoring alert
2. **Automatic**: Load balancer redirects to healthy instances
3. **Manual**: Scale up replacement instances
4. **Validation**: Verify proof functionality on new instances

#### **Database/State Loss**
1. **Impact**: Minimal (system is stateless)
2. **Recovery**: Restart services with clean state
3. **Validation**: Run integration test suite
4. **Performance**: Cache will rebuild automatically

---

## 🔍 **Troubleshooting**

### **Common Issues**

#### **Issue: SerAPI Connection Failures**
**Symptoms**: HTTP 500 errors, "No available Coq sessions" messages
**Diagnosis**:
```bash
# Check session pool status
curl http://localhost:8088/health | jq '.session_pool'

# Check logs
tail -f logs/pxl-server.log
```
**Solution**:
- Increase `PXL_POOL_SIZE` environment variable
- Restart service to reinitialize session pool
- Verify Coq/SerAPI installation

#### **Issue: High Latency (P95 > 300ms)**
**Symptoms**: Slow proof responses, timeout errors
**Diagnosis**:
```bash
# Check performance metrics
curl http://localhost:8088/metrics | jq '.logos_pxl_p95_latency_ms'

# Monitor cache hit rate
curl http://localhost:8088/metrics | jq '.logos_pxl_cache_hit_rate_percent'
```
**Solution**:
- Increase cache TTL: `PXL_CACHE_TTL=600`
- Scale session pool: `PXL_POOL_SIZE=10`
- Add more instances for load distribution

#### **Issue: HMAC Authentication Failures**
**Symptoms**: HTTP 401 errors, "Invalid signature" messages
**Diagnosis**:
```bash
# Verify secret key is set
env | grep HMAC_SECRET_KEY

# Check authentication is enabled
env | grep ENABLE_HMAC_AUTH
```
**Solution**:
- Verify client-side signature generation
- Check timestamp synchronization (±60s window)
- Ensure nonce uniqueness in high-frequency requests

### **Debug Mode**
```bash
# Enable debug logging
export LOG_LEVEL=DEBUG

# Start with verbose output
python serve_pxl.py --debug

# Monitor detailed performance
curl http://localhost:8088/metrics/performance
```

---

## 📋 **Production Checklist**

### **Pre-Deployment**
- [ ] Environment variables configured
- [ ] HMAC secret key generated and secured
- [ ] SSL/TLS certificates installed
- [ ] Monitoring and alerting configured
- [ ] Backup procedures tested
- [ ] Load testing completed (P95 < 300ms verified)

### **Post-Deployment**
- [ ] Health checks passing
- [ ] Metrics collection active
- [ ] Performance within targets
- [ ] Security validation completed
- [ ] Integration tests passed
- [ ] Documentation updated

### **Ongoing Operations**
- [ ] Monitor verification ratio (≥94%)
- [ ] Track P95 latency (<300ms)
- [ ] Maintain cache hit rate (≥85%)
- [ ] Review security logs
- [ ] Update dependencies regularly
- [ ] Backup configurations

---

## 📞 **Support and Maintenance**

### **Performance Targets**
- **Verification Ratio**: ≥94% (production threshold)
- **P95 Latency**: <300ms (sub-second response)
- **Cache Hit Rate**: ≥85% (efficiency target)
- **Uptime**: 99.9% (production availability)

### **Contact Information**
- **Technical Issues**: Create GitHub issue with logs and configuration
- **Security Concerns**: Follow responsible disclosure process
- **Performance Questions**: Include metrics output and load characteristics

### **Version Updates**
```bash
# Check current version
curl http://localhost:8088/health | jq '.kernel_hash'

# Update to new version
git checkout v0.5-rc2
docker build -t logos-pxl-core:v0.5-rc2 .
# Follow rolling update procedures
```

---

**End of Deployment Guide**

*This guide ensures successful production deployment of LOGOS_PXL_Core v0.5 with enterprise-grade security, performance, and reliability.*
