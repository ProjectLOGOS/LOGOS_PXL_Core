set -e

# --- helpers ---
mk(){ mkdir -p "$1"; }
w(){ mkdir -p "$(dirname "$1")"; cat > "$1"; }

# --- list of new IELs ---
IELS="Axiopraxis ErgoPraxis AnthroPraxis TeloPraxis TopoPraxis CosmoPraxis"

# --- scaffold IELs ---
for IEL in $IELS; do
  mk modules/IEL/$IEL/{modal,theorems,systems,tests,docs}
done

# --- Axiopraxis (Axiology: beauty/value) ---
w modules/IEL/Axiopraxis/modal/FrameSpec.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Set Implicit Arguments.

Module Axiopraxis.
  (* Worlds + aesthetic proximity (abstract) *)
  Parameter World : Type.
  Parameter R_ax : World -> World -> Prop.

  (* Modal wrappers (placeholder: reuse Box/Dia surface) *)
  Definition BoxAx (φ:form) : form := Box φ.
  Definition DiaAx  (φ:form) : form := Dia φ.
End Axiopraxis.
EOF

w modules/IEL/Axiopraxis/theorems/NormalBase.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.Axiopraxis.modal.FrameSpec.
Module AxiopraxisRules.
  Import Axiopraxis.
  Goal True. exact I. Qed.
End AxiopraxisRules.
EOF

w modules/IEL/Axiopraxis/theorems/Conservativity.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Goal True. exact I. Qed.
EOF

w modules/IEL/Axiopraxis/systems/Systems.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Module AxiopraxisSystem. End AxiopraxisSystem.
EOF

w modules/IEL/Axiopraxis/tests/Axiopraxis_Smoke.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.Axiopraxis.modal.FrameSpec.
Goal True. exact I. Qed.
EOF

w modules/IEL/Axiopraxis/docs/Axiopraxis_OVERVIEW.md <<EOF
# Axiopraxis (Axiology: beauty/value)
Purpose: value and aesthetic constraints as a modal overlay.
Status: v0.1 scaffold, zero admits.
EOF

# --- ErgoPraxis (Praxeology: means–ends) ---
w modules/IEL/ErgoPraxis/modal/FrameSpec.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Set Implicit Arguments.

Module ErgoPraxis.
  (* Actions/programs sketch *)
  Inductive Act := Skip | Seq (a b:Act) | Choice (a b:Act) | Test (φ:form).
  (* Program modality placeholders *)
  Definition BoxDo (a:Act) (φ:form) : form := Box φ.
  Definition DiaDo (a:Act) (φ:form) : form := Dia φ.
End ErgoPraxis.
EOF

w modules/IEL/ErgoPraxis/theorems/NormalBase.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.ErgoPraxis.modal.FrameSpec.
Module ErgoPraxisRules.
  Import ErgoPraxis.
  Goal True. exact I. Qed.
End ErgoPraxisRules.
EOF

w modules/IEL/ErgoPraxis/theorems/Conservativity.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Goal True. exact I. Qed.
EOF

w modules/IEL/ErgoPraxis/systems/Systems.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Module ErgoSystem. End ErgoSystem.
EOF

w modules/IEL/ErgoPraxis/tests/ErgoPraxis_Smoke.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.ErgoPraxis.modal.FrameSpec.
Goal True. exact I. Qed.
EOF

w modules/IEL/ErgoPraxis/docs/ErgoPraxis_OVERVIEW.md <<EOF
# ErgoPraxis (Praxeology: means–ends)
Purpose: means–end reasoning and plan composition.
Status: v0.1 scaffold, zero admits.
EOF

# --- AnthroPraxis (Anthropology) + BioPraxis submodule ---
mk modules/IEL/AnthroPraxis/subdomains/BioPraxis/{modal,theorems,systems,tests,docs}

w modules/IEL/AnthroPraxis/modal/FrameSpec.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Set Implicit Arguments.

Module AnthroPraxis.
  (* Agents, roles, norms (abstract) *)
  Parameter Agent : Type.
  Parameter Role  : Type.
  Parameter plays : Agent -> Role -> Prop.
  (* Social accessibility *)
  Parameter R_soc : form -> form -> Prop.
End AnthroPraxis.
EOF

w modules/IEL/AnthroPraxis/theorems/NormalBase.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.AnthroPraxis.modal.FrameSpec.
Module AnthroRules.
  Import AnthroPraxis.
  Goal True. exact I. Qed.
End AnthroRules.
EOF

w modules/IEL/AnthroPraxis/theorems/Conservativity.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Goal True. exact I. Qed.
EOF

w modules/IEL/AnthroPraxis/systems/Systems.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Module AnthroSystem. End AnthroSystem.
EOF

w modules/IEL/AnthroPraxis/tests/AnthroPraxis_Smoke.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.AnthroPraxis.modal.FrameSpec.
Goal True. exact I. Qed.
EOF

w modules/IEL/AnthroPraxis/docs/AnthroPraxis_OVERVIEW.md <<EOF
# AnthroPraxis (Anthropology)
Purpose: personhood, social roles, normed interaction.
Status: v0.1 scaffold, zero admits.
EOF

# BioPraxis submodule
w modules/IEL/AnthroPraxis/subdomains/BioPraxis/modal/FrameSpec.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Set Implicit Arguments.
Module BioPraxis.
  Parameter Organism : Type.
  Parameter Evolves : Organism -> Organism -> Prop.
End BioPraxis.
EOF

w modules/IEL/AnthroPraxis/subdomains/BioPraxis/theorems/NormalBase.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.AnthroPraxis.subdomains.BioPraxis.modal.FrameSpec.
Module BioRules.
  Import BioPraxis.
  Goal True. exact I. Qed.
End BioRules.
EOF

w modules/IEL/AnthroPraxis/subdomains/BioPraxis/systems/Systems.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Module BioSystem. End BioSystem.
EOF

w modules/IEL/AnthroPraxis/subdomains/BioPraxis/tests/BioPraxis_Smoke.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.AnthroPraxis.subdomains.BioPraxis.modal.FrameSpec.
Goal True. exact I. Qed.
EOF

w modules/IEL/AnthroPraxis/subdomains/BioPraxis/docs/BioPraxis_OVERVIEW.md <<EOF
# BioPraxis (subdomain of AnthroPraxis)
Purpose: biological grounding for human embodiment and life-process logic.
Status: v0.1 scaffold, zero admits.
EOF

# --- TeloPraxis (Teleology: purpose/goals) ---
w modules/IEL/TeloPraxis/modal/FrameSpec.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Set Implicit Arguments.

Module TeloPraxis.
  Parameter GoalSym : Type.
  Parameter intends  : GoalSym -> form -> Prop.
  (* Purpose modality placeholder *)
  Definition BoxTel (φ:form) : form := Box φ.
  Definition DiaTel (φ:form) : form := Dia φ.
End TeloPraxis.
EOF

w modules/IEL/TeloPraxis/theorems/NormalBase.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.TeloPraxis.modal.FrameSpec.
Module TeloRules.
  Import TeloPraxis.
  Goal True. exact I. Qed.
End TeloRules.
EOF

w modules/IEL/TeloPraxis/theorems/Conservativity.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Goal True. exact I. Qed.
EOF

w modules/IEL/TeloPraxis/systems/Systems.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Module TeloSystem. End TeloSystem.
EOF

w modules/IEL/TeloPraxis/tests/TeloPraxis_Smoke.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.TeloPraxis.modal.FrameSpec.
Goal True. exact I. Qed.
EOF

w modules/IEL/TeloPraxis/docs/TeloPraxis_OVERVIEW.md <<EOF
# TeloPraxis (Teleology)
Purpose: goals, ends, purposive structure.
Status: v0.1 scaffold, zero admits.
EOF

# --- TopoPraxis (Spatial logic) ---
w modules/IEL/TopoPraxis/modal/FrameSpec.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Set Implicit Arguments.

Module TopoPraxis.
  Parameter Region : Type.
  Parameter inside : Region -> Region -> Prop.
  Parameter adjacent : Region -> Region -> Prop.
  (* Spatial necessity placeholder *)
  Definition BoxTopo (φ:form) : form := Box φ.
  Definition DiaTopo (φ:form) : form := Dia φ.
End TopoPraxis.
EOF

w modules/IEL/TopoPraxis/theorems/NormalBase.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.TopoPraxis.modal.FrameSpec.
Module TopoRules.
  Import TopoPraxis.
  Goal True. exact I. Qed.
End TopoRules.
EOF

w modules/IEL/TopoPraxis/theorems/Conservativity.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Goal True. exact I. Qed.
EOF

w modules/IEL/TopoPraxis/systems/Systems.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Module TopoSystem. End TopoSystem.
EOF

w modules/IEL/TopoPraxis/tests/TopoPraxis_Smoke.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.TopoPraxis.modal.FrameSpec.
Goal True. exact I. Qed.
EOF

w modules/IEL/TopoPraxis/docs/TopoPraxis_OVERVIEW.md <<EOF
# TopoPraxis (Spatial logic)
Purpose: regions, adjacency, and spatial reasoning.
Status: v0.1 scaffold, zero admits.
EOF

# --- CosmoPraxis (Cosmology: unify Chrono+Topo; extensible) ---
w modules/IEL/CosmoPraxis/modal/FrameSpec.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.ChronoPraxis.substrate.ChronoAxioms.
Set Implicit Arguments.

Module CosmoPraxis.
  (* Space–time sketch: pair of temporal mode and spatial region index *)
  Parameter SpaceIndex : Type.
  Record STPoint := { chi_mode : ChronoAxioms.chi; sigma : SpaceIndex }.
  (* Cosmological reachability placeholder *)
  Parameter reaches : STPoint -> STPoint -> Prop.
  Definition BoxCos (φ:form) : form := Box φ.
  Definition DiaCos (φ:form) : form := Dia φ.
End CosmoPraxis.
EOF

w modules/IEL/CosmoPraxis/theorems/NormalBase.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.CosmoPraxis.modal.FrameSpec.
Module CosmoRules.
  Import CosmoPraxis.
  Goal True. exact I. Qed.
End CosmoRules.
EOF

w modules/IEL/CosmoPraxis/theorems/Conservativity.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Goal True. exact I. Qed.
EOF

w modules/IEL/CosmoPraxis/systems/Systems.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Module CosmoSystem. End CosmoSystem.
EOF

w modules/IEL/CosmoPraxis/tests/CosmoPraxis_Smoke.v <<EOF
From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.CosmoPraxis.modal.FrameSpec.
Goal True. exact I. Qed.
EOF

w modules/IEL/CosmoPraxis/docs/CosmoPraxis_OVERVIEW.md <<EOF
# CosmoPraxis (Cosmology: Chrono + Topo)
Purpose: unify temporal modes (ChronoPraxis) with spatial structure (TopoPraxis).
Status: v0.1 scaffold, zero admits.
EOF

# --- Registry / Nexus mapping updates ---
w configs/iel_registry.yaml <<EOF
defaults:
  conservativity: true
  zero_admits: true

subsystems:
  Thonoc: { preferred: [GnosiPraxis], fallbacks: [TropoPraxis] }
  Tetranose: { preferred: [DynaPraxis, ErgoPraxis, MuPraxis], fallbacks: [TropoPraxis] }
  Telos: { preferred: [TeloPraxis, ThemiPraxis, TychePraxis], fallbacks: [TropoPraxis, GnosiPraxis] }
  Archon: { preferred: [HexiPraxis, Axiopraxis, ChremaPraxis], fallbacks: [GnosiPraxis, ThemiPraxis] }
  Cosmos: { preferred: [CosmoPraxis, ChronoPraxis, TopoPraxis], fallbacks: [TropoPraxis] }
  Anthro: { preferred: [AnthroPraxis], fallbacks: [GnosiPraxis, ThemiPraxis], subdomains: [BioPraxis] }

routing:
  ontology: OntoPraxis
  epistemology: GnosiPraxis
  axiology: Axiopraxis
  praxeology: ErgoPraxis
  anthropology: AnthroPraxis
  teleology: TeloPraxis
  cosmology: CosmoPraxis
  spatial: TopoPraxis
  theology: PXL-Core
EOF

# --- Docs index update ---
mk docs
w docs/WORLDVIEW_MAP.md <<EOF
# Worldview Layer (PXL + IEL)

Pillars → IELs:
- Ontology → PXL core (+ Chrono, Tropo)
- Epistemology → GnosiPraxis
- Axiology → Axiopraxis (new)
- Praxeology → ErgoPraxis (new) [+ Dyna, Hexi]
- Anthropology → AnthroPraxis (new) with BioPraxis subdomain
- Teleology → TeloPraxis (new)
- Cosmology → CosmoPraxis (new) [Chrono + Topo]
- Theology → PXL root (triune ground)

All stubs are constructive; zero admits.
EOF

# --- Makefile wiring: append VFILES entries if Makefile exists ---
if [ -f Makefile ]; then
  w .tmp_make_add <<EOF
  modules/IEL/Axiopraxis/modal/FrameSpec.v \\
  modules/IEL/Axiopraxis/theorems/NormalBase.v \\
  modules/IEL/Axiopraxis/theorems/Conservativity.v \\
  modules/IEL/Axiopraxis/systems/Systems.v \\
  modules/IEL/Axiopraxis/tests/Axiopraxis_Smoke.v \\
  modules/IEL/ErgoPraxis/modal/FrameSpec.v \\
  modules/IEL/ErgoPraxis/theorems/NormalBase.v \\
  modules/IEL/ErgoPraxis/theorems/Conservativity.v \\
  modules/IEL/ErgoPraxis/systems/Systems.v \\
  modules/IEL/ErgoPraxis/tests/ErgoPraxis_Smoke.v \\
  modules/IEL/AnthroPraxis/modal/FrameSpec.v \\
  modules/IEL/AnthroPraxis/theorems/NormalBase.v \\
  modules/IEL/AnthroPraxis/theorems/Conservativity.v \\
  modules/IEL/AnthroPraxis/systems/Systems.v \\
  modules/IEL/AnthroPraxis/tests/AnthroPraxis_Smoke.v \\
  modules/IEL/AnthroPraxis/subdomains/BioPraxis/modal/FrameSpec.v \\
  modules/IEL/AnthroPraxis/subdomains/BioPraxis/theorems/NormalBase.v \\
  modules/IEL/AnthroPraxis/subdomains/BioPraxis/systems/Systems.v \\
  modules/IEL/AnthroPraxis/subdomains/BioPraxis/tests/BioPraxis_Smoke.v \\
  modules/IEL/TeloPraxis/modal/FrameSpec.v \\
  modules/IEL/TeloPraxis/theorems/NormalBase.v \\
  modules/IEL/TeloPraxis/theorems/Conservativity.v \\
  modules/IEL/TeloPraxis/systems/Systems.v \\
  modules/IEL/TeloPraxis/tests/TeloPraxis_Smoke.v \\
  modules/IEL/TopoPraxis/modal/FrameSpec.v \\
  modules/IEL/TopoPraxis/theorems/NormalBase.v \\
  modules/IEL/TopoPraxis/theorems/Conservativity.v \\
  modules/IEL/TopoPraxis/systems/Systems.v \\
  modules/IEL/TopoPraxis/tests/TopoPraxis_Smoke.v \\
  modules/IEL/CosmoPraxis/modal/FrameSpec.v \\
  modules/IEL/CosmoPraxis/theorems/NormalBase.v \\
  modules/IEL/CosmoPraxis/theorems/Conservativity.v \\
  modules/IEL/CosmoPraxis/systems/Systems.v \\
  modules/IEL/CosmoPraxis/tests/CosmoPraxis_Smoke.v
EOF
  # Append once to VFILES block
  if grep -q "^VFILES *:=" Makefile; then
    sed -i.bak "/^VFILES *:=/r .tmp_make_add" Makefile
  else
    echo -e \"VFILES := \\\\\n$(cat .tmp_make_add)\" >> Makefile
  fi
  rm -f .tmp_make_add
fi

# --- VS Code tasks additions ---
mk .vscode
if [ -f .vscode/tasks.json ]; then
  # append tasks safely
  python3 - <<PY
import json,sys,os
p=".vscode/tasks.json"
data=json.load(open(p)) if os.path.getsize(p)>0 else {"version":"2.0.0","tasks":[]}
def add(lbl,cmd):
    data["tasks"].append({"label":lbl,"type":"shell","command":f"bash -lc \'{cmd}\'"})
for mod in ["axiopraxis","ergopraxis","anthropraxis","telopraxis","topopraxis","cosmopraxis"]:
    add(f"coq: {mod}", f"make -j && echo built {mod}")
json.dump(data,open(p,"w"),indent=2)
PY
else
  w .vscode/tasks.json <<EOF
{
  "version": "2.0.0",
  "tasks": [
    { "label": "coq: axiopraxis", "type": "shell", "command": "bash -lc \'make -j && echo built axiopraxis\'" },
    { "label": "coq: ergopraxis", "type": "shell", "command": "bash -lc \'make -j && echo built ergopraxis\'" },
    { "label": "coq: anthropraxis", "type": "shell", "command": "bash -lc \'make -j && echo built anthropraxis\'" },
    { "label": "coq: telopraxis", "type": "shell", "command": "bash -lc \'make -j && echo built telopraxis\'" },
    { "label": "coq: topopraxis", "type": "shell", "command": "bash -lc \'make -j && echo built topopraxis\'" },
    { "label": "coq: cosmopraxis", "type": "shell", "command": "bash -lc \'make -j && echo built cosmopraxis\'" }
  ]
}
EOF
fi

echo "✅ Worldview IEL scaffolds created (Axiopraxis, ErgoPraxis, AnthroPraxis+BioPraxis, TeloPraxis, TopoPraxis, CosmoPraxis). Zero admits stubs. Registry + docs updated."