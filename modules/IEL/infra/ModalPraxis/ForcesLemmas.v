From PXLs.IEL.Infra.TropoPraxis Require Import Tropo.
From PXLs.IEL.Infra.ChronoPraxis Require Import Core.
From PXLs.IEL.Infra.ModalPraxis.theorems Require Import NormalBase.

Section ForcesBindings.
  Context {W:Type} (R:W->W->Prop) (forces: W -> Prop -> Prop).

  (* Bind to NormalBase parameters *)
  Lemma forces_mp_pxl : forall w φ ψ, forces w (φ -> ψ) -> forces w φ -> forces w ψ.
  Proof. intros w φ ψ H1 H2. apply (proj2 (forces_impl w φ ψ) H1 H2). Qed.

  Lemma forces_K_pxl : forall w φ ψ, forces w (φ -> ψ) -> forces w φ -> forces w ψ.
  Proof. apply forces_mp_pxl. Qed.  (* same as mp *)

  Global Instance CapForcesImpl_inst : Cap_ForcesImpl W R forces :=
    {| forces_impl_mp := forces_mp_pxl |}.

  Global Instance CapForcesBox_inst : Cap_ForcesBox W R forces :=
    {| forces_box_K := fun w φ ψ Hf Hφ => forces_K_pxl w φ ψ Hf Hφ
     ; forces_box_N := fun w φ H => valid_necessitation φ w H |}.

  Lemma forces_monotone_pxl :
    forall w φ ψ, (forall v, forces v (φ -> ψ)) -> forces w φ -> forces w ψ.
  Proof.
    intros w φ ψ Hvalid Hφ. specialize (Hvalid w). eapply forces_mp_pxl; eauto.
  Qed.

  Global Instance CapForcesDia_inst : Cap_ForcesDia W R forces :=
    {| forces_dia_monotone := forces_monotone_pxl |}.
End ForcesBindings.
