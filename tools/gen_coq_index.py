#!/usr/bin/env python3
import os, pathlib, re, sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "docs" / "COQ_INDEX.md"

def list_v_files(base):
    return sorted(str(p.relative_to(ROOT)).replace("\\","/") for p in ROOT.glob(base) if "_experimental" not in str(p))

def section(title, items):
    out = [f"## {title}", ""]
    if not items:
        out.append("_None detected_")
    else:
        for it in items:
            out.append(f"- `{it}`")
    out.append("")
    return "\n".join(out)

def main():
    # Heuristics: core vs overlays by path
    core = list_v_files("pxl-minimal-kernel-main/coq/**/*.v")
    overlays = list_v_files("modules/**/*.v")
    misc = [p for p in list_v_files("**/*.v") if p not in core and p not in overlays and not p.startswith(".git/")]

    header = "# Coq Source Index\n\n_Auto-generated. Do not edit by hand. Run `make docs-index`._\n"
    body = []
    body.append(section("PXL Core (kernel)", core))
    body.append(section("IEL Overlays and Domains", overlays))
    body.append(section("Miscellaneous Coq Files", misc))

    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(header + "\n".join(body), encoding="utf-8")
    print(f"Wrote {OUT}")

if __name__ == "__main__":
    main()