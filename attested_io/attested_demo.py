import json, os
from attested_io.attested_io import AttestedIO
def _sig(payload: bytes)->str:
    import hashlib; return hashlib.sha256(payload).hexdigest()[:16]
def demo_attestation():
    aio = AttestedIO({"keyA":"pubA"})
    payload = b'{"claim":"high_stakes"}'
    sig = _sig(payload)
    ok = aio.verify(payload, sig, "keyA")
    prov = aio.provenance("keyA") if ok else {"attested": False}
    print(json.dumps({"attested_ok": ok, "provenance": prov}))
if __name__ == "__main__": demo_attestation()
