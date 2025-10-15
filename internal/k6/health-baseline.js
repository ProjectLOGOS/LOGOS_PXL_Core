// k6 Load Test for LOGOS Tool Router
// Tests health endpoint baseline performance
// Usage: k6 run k6/health-baseline.js

import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate, Trend, Counter } from 'k6/metrics';

// Custom metrics
const errorRate = new Rate('error_rate');
const requestDuration = new Trend('request_duration', true);
const requestCount = new Counter('request_count');

// Test configuration
export const options = {
  vus: 20,              // Virtual users
  duration: '2m',       // Test duration
  thresholds: {
    http_req_duration: ['p(95)<500'],  // 95% of requests under 500ms
    http_req_failed: ['rate<0.01'],    // Error rate under 1%
    error_rate: ['rate<0.01'],
  },
};

const BASE_URL = __ENV.TOOL_ROUTER_URL || 'http://localhost:8071';

export default function () {
  // Test health endpoint
  const response = http.get(`${BASE_URL}/health`);
  
  // Record metrics
  requestCount.add(1);
  requestDuration.add(response.timings.duration);
  errorRate.add(response.status !== 200);
  
  // Validate response
  const success = check(response, {
    'status is 200': (r) => r.status === 200,
    'response time < 500ms': (r) => r.timings.duration < 500,
    'response has status field': (r) => {
      try {
        return JSON.parse(r.body).status !== undefined;
      } catch {
        return false;
      }
    },
  });
  
  if (!success) {
    console.error(`Health check failed: ${response.status} ${response.body}`);
  }
  
  // Brief pause between requests
  sleep(0.1);
}

export function handleSummary(data) {
  return {
    'k6-results.json': JSON.stringify(data, null, 2),
    stdout: `
🚀 LOGOS Tool Router Load Test Results
======================================

📊 Performance Summary:
• Virtual Users: ${data.options.vus}
• Duration: ${data.options.duration}
• Total Requests: ${data.metrics.http_reqs.values.count}
• Request Rate: ${(data.metrics.http_reqs.values.rate || 0).toFixed(2)} req/s

⏱️  Response Times:
• Average: ${(data.metrics.http_req_duration.values.avg || 0).toFixed(2)}ms
• 95th Percentile: ${(data.metrics.http_req_duration.values['p(95)'] || 0).toFixed(2)}ms
• 99th Percentile: ${(data.metrics.http_req_duration.values['p(99)'] || 0).toFixed(2)}ms

✅ Success Metrics:
• Success Rate: ${(100 - (data.metrics.http_req_failed.values.rate || 0) * 100).toFixed(2)}%
• Error Rate: ${((data.metrics.http_req_failed.values.rate || 0) * 100).toFixed(2)}%

${data.metrics.http_req_duration.values['p(95)'] < 500 ? '✅' : '❌'} SLO: p95 latency < 500ms
${data.metrics.http_req_failed.values.rate < 0.01 ? '✅' : '❌'} SLO: error rate < 1%

🎯 Next Steps:
• Run with signing: SIGNING_SECRET=secret k6 run k6/signed-requests.js
• Load test routing: k6 run k6/route-load.js
• Monitor metrics: curl http://localhost:8071/metrics
`,
  };
}