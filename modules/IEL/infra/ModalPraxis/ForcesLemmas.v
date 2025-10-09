From PXLs.IEL.Infra.TropoPraxis Require Import Tropo.
From PXLs.IEL.Infra.ChronoPraxis Require Import Core.
From PXLs.IEL.Infra.ModalPraxis.theorems Require Import NormalBase.

Section ForcesCaps.
  Context {W:Type} (R: W -> W -> Prop) (forces: W -> Prop -> Prop).

  Hypothesis forces_mp :
    forall w φ ψ, forces w (φ -> ψ) -> forces w φ -> forces w ψ.
  Hypothesis forces_K :
    forall w φ ψ, (* validity (□(φ->ψ) -> (□φ -> □ψ)) in your encoding *) True.

  Global Instance CapForcesImpl_inst : Cap_ForcesImpl W R forces :=
    {| forces_impl_mp := forces_mp |}.

  Global Instance CapForcesBox_inst : Cap_ForcesBox W R forces :=
    {| forces_box_K := fun w φ ψ Hf Hφ => forces_mp w φ ψ Hf Hφ
     ; forces_box_N := fun w φ _ => φ (* adjust to your validity encoding *) |}.
End ForcesCaps.