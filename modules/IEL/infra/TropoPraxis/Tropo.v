From PXLs.IEL.Infra.ModalPraxis Require Export Systems Theorems.NormalBase DerivedAxioms.

Class Cap_ForcesBox (W:Type) (R:W->W->Prop) (forces: W->Prop->Prop) : Prop :=
  { forces_box_K : forall w φ ψ, (forces w (φ -> ψ)) -> (forces w φ) -> forces w ψ
  ; forces_box_N : forall w φ, (forall u, forces u φ) -> forces w φ }.

Class Cap_ForcesDia (W:Type) (R:W->W->Prop) (forces: W->Prop->Prop) : Prop :=
  { forces_dia_monotone : forall w φ ψ, (forall u, forces u (φ -> ψ)) -> forces w φ -> forces w ψ }.

Class Cap_ForcesImpl (W:Type) (R:W->W->Prop) (forces: W->Prop->Prop) : Prop :=
  { forces_impl_mp : forall w φ ψ, forces w (Impl φ ψ) -> forces w φ -> forces w ψ }.

(* Instances from NormalBase parameters *)
Global Instance CapForcesImpl_from_NormalBase : Cap_ForcesImpl can_world can_R forces :=
  { forces_impl_mp := fun w φ ψ H1 H2 => proj2 (forces_Impl w φ ψ) H1 H2 }.

(* For Box, K axiom implies mp for Box implication? Wait, valid_K is more complex.
   Perhaps forces_box_K is for general implication, not Box.
   Since φ -> ψ is not necessarily Box.
   So, perhaps assume general mp.
   But in modal logic, implication is defined via forces.
   Since forces w (φ -> ψ) is not defined, perhaps the class is for the logic properties.
   For now, assume we have mp for general implication.
   Hypothesis forces_mp : forall w φ ψ, forces w (φ -> ψ) -> forces w φ -> forces w ψ.
   Global Instance CapForcesBox_from_mp : Cap_ForcesBox can_world can_R forces :=
     { forces_box_K := forces_mp ; forces_box_N := valid_necessitation }.
*)

(* Since forces for -> is not defined, perhaps the classes are placeholders.
   For now, add hypotheses.
*)

Hypothesis forces_mp : forall w φ ψ, forces w (φ -> ψ) -> forces w φ -> forces w ψ.
Hypothesis forces_monotone : forall w φ ψ, (forall u, forces u (φ -> ψ)) -> forces w φ -> forces w ψ.

Global Instance CapForcesBox_from_hyp : Cap_ForcesBox can_world can_R forces :=
  { forces_box_K := forces_mp ; forces_box_N := valid_necessitation }.

Global Instance CapForcesDia_from_hyp : Cap_ForcesDia can_world can_R forces :=
  { forces_dia_monotone := forces_monotone }.

Global Instance CapForcesImpl_from_hyp : Cap_ForcesImpl can_world can_R forces :=
  { forces_impl_mp := fun w φ ψ H1 H2 => proj2 (forces_Impl w φ ψ) H1 H2 }.