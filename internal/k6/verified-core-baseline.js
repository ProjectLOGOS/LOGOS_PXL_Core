import http from 'k6/http';
import { check, sleep } from 'k6';

export let options = {
  stages: [
    { duration: '2m', target: 100 }, // Ramp up to 100 users over 2 minutes
    { duration: '5m', target: 100 }, // Stay at 100 users for 5 minutes
    { duration: '2m', target: 200 }, // Ramp up to 200 users over 2 minutes
    { duration: '5m', target: 200 }, // Stay at 200 users for 5 minutes
    { duration: '2m', target: 0 },   // Ramp down to 0 users
  ],
  thresholds: {
    http_req_duration: ['p(99)<1500'], // 99% of requests should be below 1.5s
    http_req_failed: ['rate<0.1'],     // Error rate should be below 10%
  },
};

const BASE_URL = __ENV.BASE_URL || 'http://localhost:8080';

export default function () {
  // Health check
  let healthResponse = http.get(`${BASE_URL}/health`);
  check(healthResponse, {
    'health status is 200': (r) => r.status === 200,
    'health has verified flag': (r) => r.json().verified === true,
    'health has coqchk header': (r) => r.headers['X-PXL-Coqchk'] !== undefined,
    'health has build SHA header': (r) => r.headers['X-Build-SHA'] === '40360dc',
    'health has release tag header': (r) => r.headers['X-Release-Tag'] === 'v3.0.0-verified',
  });

  // Proof ping check
  let pingResponse = http.get(`${BASE_URL}/proof/ping`);
  check(pingResponse, {
    'ping status is 200': (r) => r.status === 200,
    'ping has verified core loaded': (r) => r.json().ping === 'verified_core_loaded',
    'ping has coqchk header': (r) => r.headers['X-PXL-Coqchk'] !== undefined,
    'ping has build SHA header': (r) => r.headers['X-Build-SHA'] === '40360dc',
  });

  sleep(Math.random() * 2 + 1); // Random sleep between 1-3 seconds
}

export function handleSummary(data) {
  return {
    'stdout': textSummary(data, { indent: ' ', enableColors: true }),
    'verified-core-baseline.json': JSON.stringify(data, null, 2),
  };
}
