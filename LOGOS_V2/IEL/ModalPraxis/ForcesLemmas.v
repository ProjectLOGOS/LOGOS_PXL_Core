(* From PXLs.Internal Emergent Logics.Infra.TropoPraxis Require Import Tropo. *)
From PXLs.Internal Emergent Logics.Infra.ChronoPraxis Require Import Core.
From PXLs.Internal Emergent Logics.Infra.ModalPraxis.theorems Require Import NormalBase.

Section ForcesBindings.
  Context {W:Type} (R:W->W->Prop) (forces: W -> form -> Prop).
  Parameter forces_Impl : forall w φ ψ, forces w (Impl φ ψ) <-> (forces w φ -> forces w ψ).
  Parameter forces_Box : forall w φ, forces w (Box φ) <-> (forall u, R w u -> forces u φ).
  Parameter forces_Dia : forall w φ, forces w (Dia φ) <-> (exists u, R w u /\ forces u φ).

  (* Bind to NormalBase parameters *)
  Lemma forces_mp_pxl : forall w φ ψ, forces w (Impl φ ψ) -> forces w φ -> forces w ψ.
  Proof. intros w φ ψ H1 H2. exact ((proj1 (forces_Impl w φ ψ) H1) H2). Qed.

  Lemma forces_K_pxl : forall w φ ψ, forces w (Impl φ ψ) -> forces w φ -> forces w ψ.
  Proof. apply forces_mp_pxl. Qed.  (* same as mp *)

  Global Instance CapForcesImpl_inst : Cap_ForcesImpl W R forces :=
    {| forces_impl := forces_Impl |}.

  Global Instance CapForcesBox_inst : Cap_ForcesBox W R forces :=
    {| forces_box := forces_Box |}.

  Global Instance CapForcesDia_inst : Cap_ForcesDia W R forces :=
    {| forces_dia := forces_Dia |}.
End ForcesBindings.
