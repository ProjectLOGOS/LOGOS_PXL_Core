def test_router_determinism():
    import subprocess, hashlib, pathlib
    p = pathlib.Path("config/ontological_properties.json").read_bytes()
    h1 = hashlib.sha256(p).hexdigest()
    subprocess.run(["python","tools/audit_and_emit.py","--write"], check=True)
    h2 = hashlib.sha256(pathlib.Path("config/ontological_properties.json").read_bytes()).hexdigest()
    assert h1 == h2