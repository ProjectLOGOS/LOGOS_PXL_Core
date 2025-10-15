#!/usr/bin/env bash
set -euo pipefail

echo "🧪 LOGOS API Smoke Test"
echo "======================="

base="${LOGOS_API_URL:-http://localhost:8090}"

echo "1. Testing health endpoint..."
curl -fsS "$base/health"
echo "✅ Health check passed"

echo ""
echo "2. Testing authorize_action endpoint..."
resp="$(curl -fsS -H 'content-type: application/json' -d '{"action":"cluster_texts","state":{}}' "$base/authorize_action")"
echo "$resp" | jq .
echo "✅ Authorization successful"

echo ""
echo "3. Testing verify_kernel endpoint..."
curl -fsS -H 'content-type: application/json' -d '{"kernel_hash": "deadbeef"}' "$base/verify_kernel" | jq .
echo "✅ Kernel verification working"

echo ""
echo "4. Testing proof token structure..."
token_data=$(echo "$resp" | jq -r '.proof_token')
if echo "$token_data" | jq -e '.token and .exp and .action_sha256 and .nonce' > /dev/null; then
    echo "✅ Proof token has all required fields"
else
    echo "❌ Proof token missing required fields"
    exit 1
fi

echo ""
echo "🎉 All LOGOS API smoke tests passed!"
echo "API is ready for integration with tool router and chat services."