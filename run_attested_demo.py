import hashlib
import json
import sys

sys.path.append(".")
from attested_io import AttestedIO

aio = AttestedIO({"keyA": "pubA"})
payload = b'{"claim":"high_stakes"}'
sig = hashlib.sha256(payload).hexdigest()[:16]
ok = aio.verify(payload, sig, "keyA")
prov = aio.provenance("keyA") if ok else {"attested": False}
print(json.dumps({"attested_ok": ok, "provenance": prov}, indent=2))
