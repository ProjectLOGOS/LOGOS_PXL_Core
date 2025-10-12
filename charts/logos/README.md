# LOGOS Kubernetes Deployment

This Helm chart deploys the complete LOGOS AGI system to Kubernetes, including the Enhanced Tool Router v2.0.0, LOGOS Core API, Interactive Chat interface, and optional Redis for distributed rate limiting.

## Prerequisites

- Kubernetes 1.19+
- Helm 3.2.0+
- kubectl configured to access your cluster

## Installation

### Basic Installation

```bash
# Add the repository (if using a remote chart)
helm repo add logos https://your-repo.com/charts
helm repo update

# Install from local directory
helm install logos ./charts/logos

# Or install with custom values
helm install logos ./charts/logos -f custom-values.yaml
```

### Production Installation with Secrets

```bash
# Create namespace
kubectl create namespace logos-system

# Install with signing secrets
helm install logos ./charts/logos \
  --namespace logos-system \
  --set global.signingSecret="your-secret-key-here" \
  --set global.apiSigningSecret="your-api-secret-key-here" \
  --set global.useRedisLimiter=true \
  --set ingress.enabled=true \
  --set ingress.hosts[0].host="logos.yourdomain.com"
```

## Configuration

### Key Values

| Parameter | Description | Default |
|-----------|-------------|---------|
| `global.signingSecret` | HMAC signing secret for tool router | `""` |
| `global.apiSigningSecret` | HMAC signing secret for LOGOS API | `""` |
| `global.useRedisLimiter` | Enable Redis for distributed rate limiting | `false` |
| `toolRouter.replicaCount` | Number of tool router replicas | `2` |
| `logosApi.replicaCount` | Number of LOGOS API replicas | `1` |
| `interactiveChat.replicaCount` | Number of chat interface replicas | `1` |

### Component Configuration

#### Tool Router
- Enhanced with HMAC signing, circuit breakers, retries with jitter
- Prometheus metrics on port 9090
- Configurable rate limiting (Redis or in-memory)
- Structured JSON logging with request IDs

#### LOGOS API
- Minimal FastAPI service with authorization endpoints
- Optional HMAC signing for secure communication
- Health checks and proper error handling

#### Interactive Chat
- Web interface with GPT integration
- Pattern matching fallback system
- Connects to tool router for AI functionality

### Ingress Configuration

```yaml
ingress:
  enabled: true
  className: "nginx"
  annotations:
    cert-manager.io/cluster-issuer: "letsencrypt-prod"
  hosts:
    - host: logos.example.com
      paths:
        - path: /
          pathType: Prefix
          serviceName: logos-interactive-chat
          servicePort: 80
        - path: /api
          pathType: Prefix
          serviceName: logos-logos-api
          servicePort: 80
        - path: /router
          pathType: Prefix
          serviceName: logos-tool-router
          servicePort: 80
  tls:
    - secretName: logos-tls
      hosts:
        - logos.example.com
```

### Monitoring Configuration

```yaml
monitoring:
  serviceMonitor:
    enabled: true
    interval: 30s
    scrapeTimeout: 10s
  prometheusRule:
    enabled: true
```

## Security Features

### HMAC Signing
- Configurable HMAC-SHA256 signing for API requests
- Separate secrets for tool router and LOGOS API
- Automatic signature verification

### Security Contexts
- Non-root containers with read-only file systems
- Dropped capabilities and security contexts
- Service account with minimal permissions

### Rate Limiting
- Redis-backed distributed rate limiting (recommended for production)
- In-memory fallback for single-replica deployments
- Configurable requests per minute per client

## Scaling

### Horizontal Scaling
```bash
# Scale tool router for high load
kubectl scale deployment logos-tool-router --replicas=5

# Scale LOGOS API for authorization requests
kubectl scale deployment logos-logos-api --replicas=3
```

### Resource Requests/Limits
```yaml
toolRouter:
  resources:
    requests:
      memory: "256Mi"
      cpu: "250m"
    limits:
      memory: "512Mi"
      cpu: "500m"
```

## Monitoring & Observability

### Prometheus Metrics
- HTTP request metrics with status codes and durations
- Circuit breaker state metrics
- Rate limiting metrics
- Custom business metrics

### Health Checks
- Liveness and readiness probes on all services
- Proper startup delays and timeout configuration
- Graceful degradation handling

### Logging
- Structured JSON logging with correlation IDs
- Configurable log levels
- Request/response tracing

## Troubleshooting

### Common Issues

1. **Pod Startup Issues**
   ```bash
   kubectl describe pod <pod-name>
   kubectl logs <pod-name> --previous
   ```

2. **Service Discovery Problems**
   ```bash
   kubectl get endpoints
   kubectl get services
   ```

3. **HMAC Signing Errors**
   ```bash
   kubectl get secrets
   kubectl logs deployment/logos-tool-router | grep -i hmac
   ```

### Debug Mode
```bash
# Enable debug logging
helm upgrade logos ./charts/logos \
  --set toolRouter.configData.LOG_LEVEL="DEBUG" \
  --set logosApi.configData.LOG_LEVEL="DEBUG"
```

## Upgrade

```bash
# Upgrade to new version
helm upgrade logos ./charts/logos

# Upgrade with new values
helm upgrade logos ./charts/logos -f new-values.yaml

# Rollback if needed
helm rollback logos 1
```

## Uninstallation

```bash
# Uninstall the release
helm uninstall logos

# Clean up persistent volumes if any
kubectl delete pvc -l app.kubernetes.io/instance=logos
```

## Development

### Local Development
```bash
# Template validation
helm template logos ./charts/logos

# Dry run
helm install logos ./charts/logos --dry-run

# Lint chart
helm lint ./charts/logos
```

### Custom Values Example
```yaml
# custom-values.yaml
global:
  imageRegistry: "your-registry.com"
  signingSecret: "your-secret-here"
  useRedisLimiter: true

toolRouter:
  replicaCount: 3
  resources:
    requests:
      memory: "512Mi"
      cpu: "500m"
  enableCircuitBreaker: true
  circuitBreakerFailureThreshold: 5

monitoring:
  serviceMonitor:
    enabled: true
  prometheusRule:
    enabled: true

ingress:
  enabled: true
  className: "nginx"
  hosts:
    - host: "logos.mydomain.com"
      paths:
        - path: "/"
          pathType: "Prefix"
          serviceName: "logos-interactive-chat"
          servicePort: 80
```

## Support

- Chart Version: 2.0.0
- App Version: 2.0.0
- Kubernetes Version: 1.19+
- Helm Version: 3.2.0+

For issues and support, check the logs and monitoring dashboards. The system includes comprehensive health checks and observability features to aid in troubleshooting.
