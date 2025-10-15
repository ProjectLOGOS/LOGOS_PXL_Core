From Coq Require Import Program Setoids.Setoid.

(* TODO: Restore full imports once module path resolution is fixed *)
(* From PXLs Require Import PXLv3. *)
(* Require Import modules.Internal Emergent Logics.UM.modal.FrameSpec. *)

(* Standalone loading - reuse parameters from FrameSpec *)
Parameter form : Type.
Parameter Prov : form -> Prop.
Parameter Box : form -> form.
Parameter Dia : form -> form.
Parameter Impl : form -> form -> form.

Definition set := form -> Prop.
Parameter mct : set -> Prop.
Definition can_world := { G : set | mct G }.
Parameter can_R : can_world -> can_world -> Prop.
Parameter forces : can_world -> form -> Prop.

(* Forcing relation axioms *)
Parameter forces_Box : forall w φ, forces w (Box φ) <-> (forall u, can_R w u -> forces u φ).
Parameter forces_Dia : forall w φ, forces w (Dia φ) <-> (exists u, can_R w u /\ forces u φ).
Parameter forces_Impl : forall w φ ψ, forces w (Impl φ ψ) <-> (forces w φ -> forces w ψ).

(* Modal operator capabilities *)
Class Cap_ForcesBox (W:Type) (R:W->W->Prop) (forces: W->form->Prop) : Prop :=
  { forces_box : forall w φ, forces w (Box φ) <-> (forall u, R w u -> forces u φ) }.

Class Cap_ForcesDia (W:Type) (R:W->W->Prop) (forces: W->form->Prop) : Prop :=
  { forces_dia : forall w φ, forces w (Dia φ) <-> (exists u, R w u /\ forces u φ) }.

Class Cap_ForcesImpl (W:Type) (R:W->W->Prop) (forces: W->form->Prop) : Prop :=
  { forces_impl : forall w φ ψ, forces w (Impl φ ψ) <-> (forces w φ -> forces w ψ) }.

(* Parameters replaced by instances *)
Global Instance CapForcesBox_param : Cap_ForcesBox can_world can_R forces :=
  { forces_box := fun w φ => forces_Box w φ }.

Global Instance CapForcesDia_param : Cap_ForcesDia can_world can_R forces :=
  { forces_dia := fun w φ => forces_Dia w φ }.

Global Instance CapForcesImpl_param : Cap_ForcesImpl can_world can_R forces :=
  { forces_impl := fun w φ ψ => forces_Impl w φ ψ }.

(* Remove parameters, use caps instead *)
(* Parameter forces_Box : forall w φ, forces w (Box φ) <-> (forall u, can_R w u -> forces u φ). *)
(* Parameter forces_Dia : forall w φ, forces w (Dia φ) <-> (exists u, can_R w u /\ forces u φ). *)
(* Parameter forces_Impl : forall w φ ψ, forces w (Impl φ ψ) <-> (forces w φ -> forces w ψ). *)

Parameter completeness_from_truth : forall φ, (forall w, forces w φ) -> Prov φ.

Set Implicit Arguments.

(* Necessitation: valid on all frames - no frame conditions needed *)
Lemma valid_necessitation `{Cap_ForcesBox can_world can_R forces} : forall (φ:form) (w:can_world),
  (forall u, forces u φ) -> forces w (Box φ).
Proof.
  intros φ w Hnec. rewrite forces_box.
  intros u _. exact (Hnec u).
Qed.

Theorem provable_necessitation `{Cap_ForcesBox can_world can_R forces} : forall φ,
  (forall w, forces w φ) -> Prov (Box φ).
Proof.
  intro φ. intro Hprov.
  apply completeness_from_truth. intro w.
  now apply valid_necessitation.
Qed.

(* K axiom: valid on all frames - foundation of normal modal logic *)
Lemma valid_K `{Cap_ForcesBox can_world can_R forces} `{Cap_ForcesImpl can_world can_R forces} : forall (φ ψ:form) (w:can_world),
  forces w (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
Proof.
  intros φ ψ w. rewrite forces_impl. intro HboxImp.
  rewrite forces_impl. intro Hboxφ.
  rewrite forces_box in HboxImp. rewrite forces_box in Hboxφ. rewrite forces_box.
  intros u Hwu.
  specialize (HboxImp u Hwu). rewrite forces_impl in HboxImp.
  specialize (Hboxφ u Hwu).
  exact (HboxImp Hboxφ).
Qed.

Theorem provable_K `{Cap_ForcesBox can_world can_R forces} `{Cap_ForcesImpl can_world can_R forces} : forall φ ψ, Prov (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
Proof.
  intros φ ψ. apply completeness_from_truth.
  intro w. apply valid_K.
Qed.

Lemma forces_mp_pxl : forall w φ ψ, forces w (Impl φ ψ) -> forces w φ -> forces w ψ.
Proof. intros w φ ψ H1 H2. exact ((proj1 (forces_impl w φ ψ) H1) H2). Qed.
