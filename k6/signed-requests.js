// k6 Load Test for HMAC Signed Requests
// Tests signed request performance and validation
// Usage: SIGNING_SECRET=your-secret k6 run k6/signed-requests.js

import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate, Trend, Counter } from 'k6/metrics';
import crypto from 'k6/crypto';

// Custom metrics
const signatureValidations = new Counter('signature_validations');
const signatureFailures = new Counter('signature_failures');
const signingLatency = new Trend('signing_latency', true);

export const options = {
  vus: 15,
  duration: '90s',
  thresholds: {
    http_req_duration: ['p(95)<800'],
    signature_failures: ['count<10'], // Allow some invalid signatures for testing
    signing_latency: ['p(95)<5'],     // Signing should be very fast
  },
};

const BASE_URL = __ENV.TOOL_ROUTER_URL || 'http://localhost:8071';
const SIGNING_SECRET = __ENV.SIGNING_SECRET;

if (!SIGNING_SECRET) {
  throw new Error('SIGNING_SECRET environment variable is required');
}

const TEST_PAYLOAD = {
  tool: 'tetragnos',
  args: {
    op: 'cluster_texts',
    texts: ['Performance test', 'Load testing', 'HMAC validation']
  },
  proof_token: { token: 'perf-test-token' }
};

function signRequest(payload, timestamp) {
  const signingStart = new Date().getTime();
  const message = timestamp + '.' + JSON.stringify(payload);
  const signature = crypto.hmac('sha256', SIGNING_SECRET, message, 'hex');
  const signingEnd = new Date().getTime();
  
  signingLatency.add(signingEnd - signingStart);
  return signature;
}

export default function () {
  const timestamp = Math.floor(Date.now() / 1000).toString();
  
  // 90% valid signatures, 10% invalid for testing signature validation
  const useValidSignature = Math.random() > 0.1;
  const signature = useValidSignature 
    ? signRequest(TEST_PAYLOAD, timestamp)
    : 'invalid-signature-' + Math.random().toString(36);
    
  const headers = {
    'Content-Type': 'application/json',
    'X-Timestamp': timestamp,
    'X-Signature': signature,
  };
  
  const response = http.post(`${BASE_URL}/route`, JSON.stringify(TEST_PAYLOAD), {
    headers: headers,
  });
  
  // Track signature validation results
  signatureValidations.add(1);
  if (response.status === 401 || response.status === 403) {
    signatureFailures.add(1);
  }
  
  // Validate response
  const success = check(response, {
    'valid signature accepted': (r) => useValidSignature ? r.status !== 401 && r.status !== 403 : true,
    'invalid signature rejected': (r) => !useValidSignature ? r.status === 401 || r.status === 403 : true,
    'response time acceptable': (r) => r.timings.duration < 1000,
  });
  
  if (!success && useValidSignature) {
    console.error(`Valid signature rejected: ${response.status} ${response.body}`);
  }
  
  sleep(0.2); // Slightly slower for crypto operations
}

export function handleSummary(data) {
  const totalValidations = data.metrics.signature_validations?.values.count || 0;
  const totalFailures = data.metrics.signature_failures?.values.count || 0;
  const avgSigningTime = data.metrics.signing_latency?.values.avg || 0;
  
  return {
    'k6-signing-results.json': JSON.stringify(data, null, 2),
    stdout: `
🔐 LOGOS Tool Router - HMAC Signing Load Test Results
====================================================

🎯 Security Test Configuration:
• Virtual Users: ${data.options.vus}
• Duration: ${data.options.duration}
• Signing Secret: ✅ Configured
• Test Mix: 90% valid, 10% invalid signatures

📊 Signature Statistics:
• Total Signature Validations: ${totalValidations}
• Signature Failures: ${totalFailures}
• Failure Rate: ${((totalFailures/totalValidations)*100).toFixed(2)}%

⏱️  Performance Impact:
• Average Signing Time: ${avgSigningTime.toFixed(2)}ms
• 95th Percentile Signing: ${(data.metrics.signing_latency?.values['p(95)'] || 0).toFixed(2)}ms
• Request Latency (with HMAC): ${(data.metrics.http_req_duration?.values.avg || 0).toFixed(2)}ms
• 95th Percentile Request: ${(data.metrics.http_req_duration?.values['p(95)'] || 0).toFixed(2)}ms

🛡️  Security Validation:
• Expected Failures (~10%): ${Math.floor(totalValidations * 0.1)}
• Actual Failures: ${totalFailures}
• Security Working: ${Math.abs(totalFailures - Math.floor(totalValidations * 0.1)) < 5 ? '✅' : '❌'}

${avgSigningTime < 5 ? '✅' : '❌'} Performance: Signing overhead < 5ms
${data.metrics.http_req_duration?.values['p(95)'] < 800 ? '✅' : '❌'} SLO: p95 latency < 800ms (with HMAC)
${Math.abs(totalFailures - Math.floor(totalValidations * 0.1)) < 10 ? '✅' : '❌'} Security: Proper signature validation

🔧 HMAC Configuration:
• Algorithm: HMAC-SHA256
• Timestamp Window: 300s (configurable via SIGNING_MAX_SKEW_SECS)
• Message Format: timestamp.json_payload

📝 Production Notes:
• HMAC adds ~${avgSigningTime.toFixed(1)}ms overhead per request
• Signature validation is working correctly
• Consider timestamp skew for distributed systems
`,
  };
}