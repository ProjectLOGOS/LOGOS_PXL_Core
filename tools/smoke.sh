#!/usr/bin/env bash
set -euo pipefail

echo "🔥 LOGOS PXL Core Smoke Test"
echo "============================"

# Test 1: LOGOS API Health Check
echo "1. Testing LOGOS API health..."
curl -sf http://localhost:8090/health
echo "✅ LOGOS API is healthy"

# Test 2: Get proof token for operations
echo "2. Getting proof token..."
PT=$(curl -sf -X POST http://localhost:8090/authorize_action \
  -H 'content-type: application/json' \
  -d '{"action":"cluster_texts","state":{},"provenance":{"source":"smoke"}}' | jq -r '.proof_token | @json')
echo "✅ Proof token obtained: ${PT:0:50}..."

# Test 3: Test TETRAGNOS via tool router
echo "3. Testing TETRAGNOS text clustering..."
curl -sf -X POST http://localhost:8071/route \
  -H 'content-type: application/json' \
  -d "{\"tool\":\"tetragnos\",\"args\":{\"op\":\"cluster_texts\",\"texts\":[\"Machine learning is powerful\",\"AI transforms industries\",\"Deep learning advances rapidly\"]},\"proof_token\":$PT}" | jq .
echo "✅ TETRAGNOS clustering successful"

# Test 4: Test THONOC via tool router
echo "4. Testing THONOC theorem proving..."
curl -sf -X POST http://localhost:8071/route \
  -H 'content-type: application/json' \
  -d "{\"tool\":\"thonoc\",\"args\":{\"formula\":\"A->B\"},\"proof_token\":$PT}" | jq .
echo "✅ THONOC proving successful"

# Test 5: Test interactive chat health
echo "5. Testing Interactive Chat service..."
if curl -sf http://localhost:8080/health 2>/dev/null; then
    echo "✅ Interactive Chat is healthy"
else
    echo "⚠️  Interactive Chat health check not available (may not have health endpoint)"
fi

echo ""
echo "🎉 ALL SMOKE TESTS PASSED!"
echo "Your LOGOS PXL Core system is operational and ready for use."
echo ""
echo "Next steps:"
echo "- Visit http://localhost:8080 for GPT-enhanced chat"
echo "- Use http://localhost:8071/route for tool routing"
echo "- Access http://localhost:8090/authorize_action for proof tokens"