#!/usr/bin/env python
"""Quick library status check"""

libs_to_test = [
    ('pyro', 'pyro'),
    ('torch', 'torch'),
    ('sentence_transformers', 'sentence_transformers'),
    ('networkx', 'networkx'),
    ('arch', 'arch'),
    ('filterpy', 'filterpy'),
    ('pykalman', 'pykalman'),
    ('sklearn', 'sklearn'),
    ('speech_recognition', 'speech_recognition'),
    ('pyttsx3', 'pyttsx3'),
    ('tkinter', 'tkinter'),
    ('pymc', 'pymc'),
    ('pmdarima', 'pmdarima'),
]

print("=== LOGOS Library Status Check ===\n")

loaded = []
failed = []

for name, module in libs_to_test:
    try:
        __import__(module)
        loaded.append(name)
        print(f"✅ {name}")
    except ImportError as e:
        failed.append(name)
        print(f"❌ {name} - {str(e)[:50]}")

print(f"\n=== Summary ===")
print(f"Loaded: {len(loaded)}/13 ({len(loaded)/13*100:.1f}%)")
print(f"Failed: {len(failed)}/13")

if failed:
    print(f"\nMissing libraries: {', '.join(failed)}")
