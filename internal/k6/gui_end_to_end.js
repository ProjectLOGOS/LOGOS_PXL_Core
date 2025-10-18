import http from 'k6/http';
import { check, sleep } from 'k6';
import { Rate, Trend } from 'k6/metrics';

// Custom metrics
const proofLatency = new Trend('proof_request_duration');
const overlayLatency = new Trend('overlay_request_duration');
const healthCheckRate = new Rate('health_checks_success_rate');

export const options = {
  stages: [
    { duration: '2m', target: 10 },   // Ramp up to 10 users
    { duration: '5m', target: 50 },   // Ramp up to 50 users
    { duration: '10m', target: 100 }, // Ramp up to 100 users
    { duration: '5m', target: 100 },  // Stay at 100 users
    { duration: '2m', target: 0 },    // Ramp down
  ],
  thresholds: {
    http_req_duration: ['p(95)<300'], // 95% of requests should be below 300ms
    http_req_failed: ['rate<0.05'],   // Error rate should be below 5%
    proof_request_duration: ['p(95)<500'], // Proof requests should be fast
    health_checks_success_rate: ['rate>0.99'], // Health checks should succeed 99% of time
  },
};

const BASE_URL = __ENV.BASE_URL || 'http://localhost:8080';

export default function () {
  // Health check
  const healthResponse = http.get(`${BASE_URL}/v1/health`);
  check(healthResponse, {
    'health status is 200': (r) => r.status === 200,
    'has provenance headers': (r) => r.headers['X-PXL-Coqchk'] && r.headers['X-Build-SHA'],
  });
  healthCheckRate.add(healthResponse.status === 200);

  // Proof submission
  const proofPayload = JSON.stringify({
    formula: { type: 'implies', left: 'A', right: 'B' },
    overlay: 'chrono',
    timeout: 30,
  });

  const proofResponse = http.post(`${BASE_URL}/v1/proofs`, proofPayload, {
    headers: { 'Content-Type': 'application/json' },
  });

  const proofStart = new Date(proofResponse.headers['Date']).getTime();
  const proofEnd = new Date().getTime();
  proofLatency.add(proofEnd - proofStart);

  check(proofResponse, {
    'proof submission succeeds': (r) => r.status === 200,
    'proof has verdict': (r) => JSON.parse(r.body).verdict,
    'proof has trace': (r) => JSON.parse(r.body).trace,
  });

  // Overlay operation
  const overlayPayload = JSON.stringify({
    operation: 'normalize',
    formula: { type: 'implies', left: 'A', right: 'B' },
  });

  const overlayResponse = http.post(`${BASE_URL}/v1/overlays/chrono`, overlayPayload, {
    headers: { 'Content-Type': 'application/json' },
  });

  const overlayStart = new Date(overlayResponse.headers['Date']).getTime();
  const overlayEnd = new Date().getTime();
  overlayLatency.add(overlayEnd - overlayStart);

  check(overlayResponse, {
    'overlay operation succeeds': (r) => r.status === 200,
    'overlay has result': (r) => JSON.parse(r.body).result,
    'overlay has trace': (r) => JSON.parse(r.body).chrono_trace,
  });

  // Simulate user think time
  sleep(Math.random() * 3 + 1); // 1-4 seconds
}
