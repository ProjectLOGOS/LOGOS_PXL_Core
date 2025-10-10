# Proof-Token API Specification

## Endpoint: /verify

### Input
- `formula`: JSON-serialized PXL formula
- `context`: JSON context object
- `overlay`: string, e.g. "chrono", "modal"

### Output
```json
{
  "verdict": "valid" | "invalid" | "unknown",
  "trace": ["step1", "step2"],
  "certificate": "base64_bytes" // optional
}
```

### Example
POST /verify
```json
{
  "formula": {"type": "implies", "left": "A", "right": "B"},
  "context": {},
  "overlay": "chrono"
}
```

Response:
```json
{
  "verdict": "valid",
  "trace": ["Applied chrono normalization"],
  "certificate": "proof_bytes"
}
```