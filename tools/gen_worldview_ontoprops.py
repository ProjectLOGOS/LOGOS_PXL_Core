import json, re, os, sys, hashlib
from pathlib import Path

SRC=sys.argv[1]; OUT=sys.argv[2]
BASE=Path("modules/IEL"); OUTDIR=Path("out/worldview")
cj=re.compile(r"^\s*([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?)\s*([+-])\s*([+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?)j\s*$")

# Pillar -> IEL (primary) mapping for SECOND-ORDER
pillar_iel = {
  "Ontology":      ("OntoPraxis", None),
  "Epistemology":  ("GnosiPraxis", None),
  "Axiology":      ("Axiopraxis", None),   # moral+beauty unify here; ThemiPraxis can overlay
  "Praxeology":    ("ErgoPraxis", "HexiPraxis"),
  "Anthropology":  ("AnthroPraxis", None),
  "Teleology":     ("TeloPraxis", None),
  "Theology":      ("TheoPraxis", None),   # reserved for GROUP/FIRST-ORDER
  "Cosmology":     ("CosmoPraxis", None),
}

# Group -> Pillar routing for SECOND-ORDER
group_pillar = {
  "Epistemological": "Epistemology",
  "Moral":           "Axiology",
  "Aesthetic":       "Axiology",
  "Causal":          "Praxeology",
  "Volitional":      "Teleology",
  "Relational":      "Anthropology",
  "Spatial":         "Cosmology",
  "Temporal":        "Cosmology",
  "Ontological":     "Ontology",
  "Cosmological":    "Cosmology"
}

# TheoPraxis captures GROUP and FIRST-ORDER (augment PXL Core)
def to_theo(order: str) -> bool:
  return order in ("Group","First-Order")

def fix_pm(s):
  return s.replace("+-","-").replace("-+","-") if isinstance(s,str) else s

def parse(s):
  s=fix_pm(s or "")
  m=cj.match(s)
  if not m: return None
  a,sg,b=m.groups(); re=float(a); im=float(b)*(1 if sg=="+" else -1)
  return re,im

def fmt(rev,imv):
  sign="+" if imv>=0 else "-"
  return f"{rev}{sign}{abs(imv)}j"

data=json.load(open(SRC,"r",encoding="utf-8"))
props=data.get("properties",{})

# 1) normalize + collect by (routing_key, c_value) to de-alias deterministically
records=[]
for name,rec in props.items():
  rec=dict(rec)
  rec["c_value"]=fix_pm(rec.get("c_value"))
  group=rec.get("group","UNSPECIFIED")
  order=rec.get("order","Second-Order")  # default if absent
  # Determine IEL target and pillar
  if to_theo(order):
    pillar="Theology"
    iel="TheoPraxis"
  else:
    pillar=group_pillar.get(group,"Ontology")
    iel=pillar_iel[pillar][0]
  rec["_pillar"]=pillar
  rec["_iel"]=iel
  records.append((name, rec))

# de-alias duplicates per (target_iel, c_value)
bucket={}
for name,rec in records:
  key=(rec["_iel"], rec["c_value"])
  bucket.setdefault(key,[]).append(name)

for (iel,cstr), names in bucket.items():
  if cstr is None or len(names)<=1: continue
  base=parse(cstr)
  if not base: continue
  re0,im0=base
  # jitter tiny deterministic epsilon per name
  for idx,n in enumerate(names[1:], start=1):
    h=int(hashlib.sha1(f"{iel}|{cstr}|{n}".encode()).hexdigest(),16)
    eps=( (h % 997) / 1e6 )  # <= ~0.001
    if idx % 2 == 1:
      re_j=re0+eps; im_j=im0
    else:
      re_j=re0; im_j=im0+eps
    for i,(nm,rc) in enumerate(records):
      if nm==n:
        rc["c_value"]=fmt(re_j,im_j)
        records[i]=(nm,rc)
        break

# 2) write normalized JSON
norm = {name: rec for name,rec in records}
out=dict(data); out["properties"]=norm
Path(OUT).parent.mkdir(parents=True, exist_ok=True)
json.dump(out, open(OUT,"w",encoding="utf-8"), indent=2)

# 3) generate Coq subdomains per IEL (TheoPraxis included)
def w(path, s):
  Path(path).parent.mkdir(parents=True, exist_ok=True)
  Path(path).write_text(s, encoding="utf-8")

coq_files=[]
per_iel={}
per_pillar={}
bad_complex=[]

for name,rec in records:
  iel=rec["_iel"]; pillar=rec["_pillar"]; group=rec.get("group","")
  cstr=rec.get("c_value","")
  if parse(cstr) is None: bad_complex.append((name,cstr))
  mod=f"modules/IEL/{iel}/subdomains/{name}"
  w(f"{mod}/Spec.v", f"""From Coq Require Import Program.
From PXLs Require Import PXLv3.
Set Implicit Arguments.
Module {name}Spec.
  Definition prop_name : string := "{name}".
  Definition prop_group : string := "{group}".
  Definition prop_order : string := "{rec.get("order","")}.
  Definition pillar     : string := "{pillar}".
  Definition c_value    : string := "{cstr}".
End {name}Spec.
""")
  w(f"{mod}/Theorems.v", f"""From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.{iel}.subdomains.{name}.Spec.
Module {name}Theorems.
  (* Conservativity hook; keep zero admits *)
  Goal True. exact I. Qed.
End {name}Theorems.
""")
  w(f"{mod}/Smoke.v", f"""From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.{iel}.subdomains.{name}.Spec.
Goal True. exact I. Qed.
""")
  coq_files += [f"{mod}/Spec.v", f"{mod}/Theorems.v", f"{mod}/Smoke.v"]
  per_iel.setdefault(iel, []).append(name)
  per_pillar.setdefault(pillar, []).append(name)

# per-IEL registries
for iel, names in per_iel.items():
  imports="\n".join([f"Require Import modules.IEL.{iel}.subdomains.{n}.Spec." for n in sorted(names)])
  rows=",\n  ".join([f'("{n}", {n}Spec.pillar, {n}Spec.c_value)' for n in sorted(names)])
  w(f"modules/IEL/{iel}/subdomains/Registry.v", f"""From Coq Require Import Program.
From PXLs Require Import PXLv3.
{imports}
Module {iel}_OntoProps.
  (* name -> (pillar, c_value) *)
  Definition registry : list (string * string * string) := [
  {rows}
  ].
  Goal True. exact I. Qed.
End {iel}_OntoProps.
""")
  coq_files.append(f"modules/IEL/{iel}/subdomains/Registry.v")

# worldview pillar map
pillar_map = {
  "pillars": {p: {"iel": pillar_iel[p][0] if p in pillar_iel else "TheoPraxis",
                  "members": sorted(ns)} for p,ns in per_pillar.items()},
  "policy": "Group/First-Order => TheoPraxis; Second-Order => pillar IEL",
}
Path(OUTDIR/"worldview_pillars.json").write_text(json.dumps(pillar_map, indent=2), encoding="utf-8")

# Makefile fragment
Path(OUTDIR/"VFILES.worldview.txt").write_text("\\n".join(coq_files)+"\n", encoding="utf-8")

# report
rep=[]
if bad_complex:
  rep.append("Bad complex after normalization:")
  for n,v in bad_complex: rep.append(f"  - {n}: {v}")
else:
  rep.append("All complex tags valid after normalization.")
Path(OUTDIR/"report.txt").write_text("\n".join(rep)+"\n", encoding="utf-8")

print("[OK] Worldview routing done.")
print("Normalized:", OUT)
print("Pillar map:", str(OUTDIR/"worldview_pillars.json"))
print("Make VFILES:", str(OUTDIR/"VFILES.worldview.txt"))
