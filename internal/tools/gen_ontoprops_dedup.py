import json, sys, shutil
src, out = sys.argv[1], sys.argv[2]
shutil.copy(src, out)
print(f"[OK] Copied {src} to {out}")