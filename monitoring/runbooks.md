# LOGOS Tool Router - Operational Runbooks

## Circuit Breaker Open {#circuit-breaker-open}

**Alert**: `ToolRouterCircuitBreakerOpen`
**Severity**: Critical

### Symptoms
- Circuit breaker for a specific tool has opened
- Requests to the affected tool are being rejected with 503 errors
- Circuit breaker state metric shows "open"

### Impact
- Users cannot access the affected tool (tetragnos, thonoc, telos)
- Requests fail fast instead of timing out
- Other tools remain operational

### Investigation Steps
1. **Check circuit breaker status**:
   ```bash
   curl -s http://localhost:8071/metrics | grep circuit_breaker_state
   ```

2. **Review recent failures**:
   ```bash
   curl -s http://localhost:8071/metrics | grep upstream_calls_total
   ```

3. **Check tool service health**:
   ```bash
   # Replace with affected tool URL
   curl http://localhost:8065/health  # tetragnos
   curl http://localhost:8067/health  # thonoc
   curl http://localhost:8066/health  # telos
   ```

4. **Review tool router logs**:
   ```bash
   docker logs tool-router --tail=100 | jq 'select(.level=="ERROR")'
   ```

### Resolution
1. **Fix upstream service**: Address the root cause in the failing tool service
2. **Wait for circuit recovery**: Circuit will automatically close after cooldown period (default: 30s)
3. **Manual reset** (if needed):
   ```bash
   # Restart tool router to reset all circuits
   docker restart tool-router
   ```

### Prevention
- Monitor upstream service health continuously
- Set appropriate circuit breaker thresholds
- Implement graceful degradation in upstream services

---

## High Error Rate {#high-error-rate}

**Alert**: `ToolRouterHighErrorRate`
**Severity**: Warning

### Symptoms
- 5xx error rate > 10% over 5 minutes
- Users experiencing failures when routing requests

### Investigation Steps
1. **Check error breakdown**:
   ```bash
   curl -s http://localhost:8071/metrics | grep 'requests_total{.*status="5'
   ```

2. **Review recent logs**:
   ```bash
   docker logs tool-router --tail=200 | jq 'select(.level=="ERROR" or .status >= 500)'
   ```

3. **Check system resources**:
   ```bash
   docker stats tool-router
   ```

### Common Causes
- Upstream service failures
- Network connectivity issues
- Resource exhaustion (CPU, memory)
- Database connectivity problems
- Redis connectivity issues (if using distributed rate limiting)

### Resolution
- Address upstream service issues
- Scale tool router if resource constrained
- Check network connectivity
- Review configuration for misconfigurations

---

## Rate Limit Spike {#rate-limit-spike}

**Alert**: `ToolRouterRateLimitSpike`
**Severity**: Warning

### Symptoms
- > 100 requests rate limited in 5 minutes
- Users receiving 429 Too Many Requests errors

### Investigation Steps
1. **Check rate limit metrics**:
   ```bash
   curl -s http://localhost:8071/metrics | grep rate_limited_total
   ```

2. **Review current rate limit configuration**:
   ```bash
   docker exec tool-router env | grep RATE_LIMIT
   ```

3. **Check request patterns**:
   ```bash
   docker logs tool-router --tail=100 | jq 'select(.status==429)' | head -20
   ```

### Resolution
1. **Legitimate traffic spike**: Increase rate limits temporarily
   ```bash
   # Update docker-compose.yml or environment
   export RATE_LIMIT_REQS=200
   docker restart tool-router
   ```

2. **Abuse/DoS**: Implement additional rate limiting at load balancer level

3. **Switch to Redis**: For better distributed rate limiting
   ```bash
   export USE_REDIS_RATE_LIMIT=true
   docker restart tool-router
   ```

---

## High Latency {#high-latency}

**Alert**: `ToolRouterHighLatency`
**Severity**: Warning

### Symptoms
- p95 latency > 500ms for 3+ minutes
- Users experiencing slow responses

### Investigation Steps
1. **Check latency breakdown**:
   ```bash
   curl -s http://localhost:8071/metrics | grep request_duration_seconds
   ```

2. **Check upstream latency**:
   ```bash
   # Test direct tool access
   time curl http://localhost:8065/health
   time curl http://localhost:8067/health
   time curl http://localhost:8066/health
   ```

3. **Monitor system resources**:
   ```bash
   docker stats tool-router
   top -p $(docker inspect tool-router --format '{{.State.Pid}}')
   ```

### Common Causes
- Upstream service slowdown
- Network latency
- Resource contention
- Database/Redis slowdown
- Large request/response payloads

### Resolution
- Scale upstream services if needed
- Optimize tool router resource allocation
- Check network connectivity
- Consider request/response size limits

---

## Service Down {#service-down}

**Alert**: `ToolRouterDown`
**Severity**: Critical

### Symptoms
- Tool router not responding to health checks
- All tool routing functionality unavailable

### Investigation Steps
1. **Check container status**:
   ```bash
   docker ps | grep tool-router
   docker logs tool-router --tail=50
   ```

2. **Check resource availability**:
   ```bash
   df -h  # Disk space
   free -h  # Memory
   docker system df  # Docker space
   ```

3. **Check dependencies**:
   ```bash
   docker ps | grep redis  # If using Redis rate limiting
   docker network ls
   ```

### Resolution
1. **Restart service**:
   ```bash
   docker restart tool-router
   ```

2. **Check configuration**:
   ```bash
   docker-compose config
   ```

3. **Rebuild if needed**:
   ```bash
   docker-compose up -d --build tool-router
   ```

---

## Auth Failures {#auth-failures}

**Alert**: `ToolRouterAuthFailures`
**Severity**: Warning

### Symptoms
- > 20 authentication failures (401 errors) in 5 minutes
- HMAC signature validation failures

### Investigation Steps
1. **Check auth failure patterns**:
   ```bash
   docker logs tool-router --tail=100 | jq 'select(.status==401)'
   ```

2. **Verify HMAC configuration**:
   ```bash
   docker exec tool-router env | grep SIGNING
   ```

3. **Test signature generation**:
   ```bash
   echo '{"tool":"tetragnos","args":{"op":"ping"},"proof_token":{"token":"test"}}' | \
   SIGNING_SECRET=your-secret ./tools/sign-route.sh
   ```

### Common Causes
- Client using wrong signing secret
- Clock skew between client and server
- Malformed signature generation
- Possible attack/brute force

### Resolution
1. **Verify client configuration**: Ensure clients have correct `SIGNING_SECRET`
2. **Check time synchronization**: Verify NTP sync on client/server
3. **Increase skew tolerance**: Temporarily increase `SIGNING_MAX_SKEW_SECS`
4. **Security review**: If failures persist, investigate for potential attacks

---

## Upstream Failures {#upstream-failures}

**Alert**: `ToolRouterUpstreamFailures`
**Severity**: Warning

### Symptoms
- High failure rate calling specific upstream tool
- Circuit breaker may trigger soon

### Investigation Steps
1. **Check specific tool health**:
   ```bash
   # Replace with affected tool
   curl -v http://localhost:8065/health  # tetragnos
   curl -v http://localhost:8067/health  # thonoc
   curl -v http://localhost:8066/health  # telos
   ```

2. **Review upstream call metrics**:
   ```bash
   curl -s http://localhost:8071/metrics | grep upstream_calls_total
   ```

3. **Check tool service logs**:
   ```bash
   docker logs toolkit-tetragnos --tail=100  # or affected service
   ```

### Resolution
1. **Fix upstream service**: Address root cause in failing tool
2. **Scale upstream**: If overloaded
3. **Network issues**: Check connectivity between services
4. **Configuration**: Verify tool router has correct upstream URLs

---

## SLO Dashboard Queries

Use these Prometheus queries in Grafana:

### Availability SLO (Target: 99.9%)
```promql
(sum(rate(tool_router_requests_total{status!~"5.."}[5m])) / sum(rate(tool_router_requests_total[5m]))) * 100
```

### Latency SLO (Target: p95 < 500ms)
```promql
histogram_quantile(0.95, rate(tool_router_request_duration_seconds_bucket[5m])) * 1000
```

### Error Budget Remaining
```promql
1 - ((1 - (tool_router:availability_slo / 100)) / 0.001)
```

### Request Rate
```promql
sum(rate(tool_router_requests_total[5m]))
```

### Circuit Breaker States
```promql
tool_router_circuit_breaker_state
```
