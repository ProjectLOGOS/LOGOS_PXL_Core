#!/usr/bin/env bash
set -euo pipefail
: "${SIGNING_SECRET:?SIGNING_SECRET required}"
body="$(cat)"
ts="$(date +%s)"
sig="$(python - "$SIGNING_SECRET" "$ts" <<<"$body" <<'PY'
import sys, hmac, hashlib, json
secret=sys.argv[1].encode(); ts=sys.argv[2]
body=sys.stdin.read()
msg=(ts+"."+body).encode()
print(hmac.new(secret, msg, hashlib.sha256).hexdigest())
PY
)"
curl -sS -X POST "${TOOL_ROUTER_URL:-http://localhost:8071}/route" \
  -H "content-type: application/json" -H "X-Timestamp: $ts" -H "X-Signature: $sig" \
  -d "$body"