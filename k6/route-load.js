// k6 Load Test for LOGOS Tool Router - Route Endpoint
// Tests actual tool routing under load
// Usage: k6 run k6/route-load.js

import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate, Trend, Counter } from 'k6/metrics';
import crypto from 'k6/crypto';

// Custom metrics
const errorRate = new Rate('error_rate');
const routeLatency = new Trend('route_latency', true);
const rateLimitHits = new Counter('rate_limit_hits');

export const options = {
  stages: [
    { duration: '30s', target: 10 },  // Ramp up
    { duration: '1m', target: 25 },   // Steady load
    { duration: '30s', target: 50 },  // Spike test
    { duration: '30s', target: 0 },   // Ramp down
  ],
  thresholds: {
    http_req_duration: ['p(95)<1000'], // Routes can be slower than health
    http_req_failed: ['rate<0.05'],    // 5% error rate acceptable (includes rate limits)
    route_latency: ['p(95)<1000'],
  },
};

const BASE_URL = __ENV.TOOL_ROUTER_URL || 'http://localhost:8071';
const SIGNING_SECRET = __ENV.SIGNING_SECRET || '';

// Mock proof token for testing
const MOCK_PROOF_TOKEN = {
  token: 'test-token-' + Math.random().toString(36).substring(7)
};

// Test payloads for different tools
const TEST_PAYLOADS = [
  {
    tool: 'tetragnos',
    args: {
      op: 'cluster_texts',
      texts: ['AI is powerful', 'Machine learning advances', 'Deep learning transforms']
    },
    proof_token: MOCK_PROOF_TOKEN
  },
  {
    tool: 'thonoc',
    args: {
      formula: 'A->B'
    },
    proof_token: MOCK_PROOF_TOKEN
  },
  {
    tool: 'telos',
    args: {
      query: 'test optimization query'
    },
    proof_token: MOCK_PROOF_TOKEN
  }
];

function signRequest(payload, timestamp) {
  if (!SIGNING_SECRET) return null;
  
  const message = timestamp + '.' + JSON.stringify(payload);
  return crypto.hmac('sha256', SIGNING_SECRET, message, 'hex');
}

export default function () {
  // Select random payload
  const payload = TEST_PAYLOADS[Math.floor(Math.random() * TEST_PAYLOADS.length)];
  
  // Prepare headers
  const headers = {
    'Content-Type': 'application/json',
  };
  
  // Add HMAC signature if secret provided
  if (SIGNING_SECRET) {
    const timestamp = Math.floor(Date.now() / 1000).toString();
    const signature = signRequest(payload, timestamp);
    headers['X-Timestamp'] = timestamp;
    headers['X-Signature'] = signature;
  }
  
  // Make request
  const startTime = new Date().getTime();
  const response = http.post(`${BASE_URL}/route`, JSON.stringify(payload), {
    headers: headers,
  });
  const endTime = new Date().getTime();
  
  // Record metrics
  const duration = endTime - startTime;
  routeLatency.add(duration);
  errorRate.add(response.status >= 400);
  
  if (response.status === 429) {
    rateLimitHits.add(1);
  }
  
  // Validate response
  const success = check(response, {
    'status is not 5xx': (r) => r.status < 500,
    'response time < 2s': (r) => r.timings.duration < 2000,
    'has valid JSON': (r) => {
      try {
        JSON.parse(r.body);
        return true;
      } catch {
        return false;
      }
    },
  });
  
  // Log errors (but not rate limits)
  if (response.status >= 500) {
    console.error(`Route failed: ${response.status} ${response.body}`);
  }
  
  // Realistic user behavior
  sleep(Math.random() * 0.5 + 0.1); // 0.1-0.6s between requests
}

export function handleSummary(data) {
  const routeRequests = data.metrics.http_reqs.values.count;
  const rateLimits = data.metrics.rate_limit_hits?.values.count || 0;
  const errorCount = (data.metrics.http_req_failed?.values.count || 0) - rateLimits;
  
  return {
    'k6-route-results.json': JSON.stringify(data, null, 2),
    stdout: `
🔄 LOGOS Tool Router - Route Load Test Results
==============================================

🎯 Test Configuration:
• Max Virtual Users: 50
• Test Pattern: Ramp up → Steady → Spike → Ramp down
• HMAC Signing: ${SIGNING_SECRET ? '✅ Enabled' : '❌ Disabled'}

📊 Request Statistics:
• Total Route Requests: ${routeRequests}
• Request Rate: ${(data.metrics.http_reqs.values.rate || 0).toFixed(2)} req/s
• Rate Limited: ${rateLimits} (${((rateLimits/routeRequests)*100).toFixed(1)}%)
• Actual Errors: ${errorCount}

⏱️  Route Performance:
• Average Latency: ${(data.metrics.route_latency?.values.avg || 0).toFixed(2)}ms
• 95th Percentile: ${(data.metrics.route_latency?.values['p(95)'] || 0).toFixed(2)}ms
• 99th Percentile: ${(data.metrics.route_latency?.values['p(99)'] || 0).toFixed(2)}ms

🛡️  Resilience:
• Rate Limit Hit Rate: ${((rateLimits/routeRequests)*100).toFixed(2)}%
• Error Rate (excl. rate limits): ${((errorCount/routeRequests)*100).toFixed(2)}%
• Circuit Breaker Triggers: Check /metrics for circuit_breaker_state

${data.metrics.route_latency?.values['p(95)'] < 1000 ? '✅' : '❌'} SLO: p95 route latency < 1s
${((errorCount/routeRequests)*100) < 1 ? '✅' : '❌'} SLO: error rate < 1%

🔍 Monitoring Commands:
• Circuit states: curl -s http://localhost:8071/metrics | grep circuit_breaker
• Rate limit metrics: curl -s http://localhost:8071/metrics | grep rate_limited
• Request metrics: curl -s http://localhost:8071/metrics | grep requests_total
`,
  };
}