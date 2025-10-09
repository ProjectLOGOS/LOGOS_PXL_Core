From Coq Require Import Program Setoids.Setoid.

(* TODO: Restore full imports once module path resolution is fixed *)
(* From PXLs Require Import PXLv3. *)
(* Require Import modules.IEL.UM.modal.FrameSpec. *)

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

Parameter forces_Box : forall w φ, forces w (Box φ) <-> (forall u, can_R w u -> forces u φ).
Parameter forces_Dia : forall w φ, forces w (Dia φ) <-> (exists u, can_R w u /\ forces u φ).
Parameter forces_Impl : forall w φ ψ, forces w (Impl φ ψ) <-> (forces w φ -> forces w ψ).

Parameter completeness_from_truth : forall φ, (forall w, forces w φ) -> Prov φ.

Set Implicit Arguments.

(* Necessitation: valid on all frames - no frame conditions needed *)
Lemma valid_necessitation : forall (φ:form) (w:can_world),
  (forall u, forces u φ) -> forces w (Box φ).
Proof. 
  intros φ w H. rewrite forces_Box.
  intros u _. exact (H u). 
Qed.

Theorem provable_necessitation : forall φ,
  (forall w, forces w φ) -> Prov (Box φ).
Proof. 
  intro φ. intro H. 
  apply completeness_from_truth. intro w. 
  now apply valid_necessitation. 
Qed.

(* K axiom: valid on all frames - foundation of normal modal logic *)
Lemma valid_K : forall (φ ψ:form) (w:can_world),
  forces w (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
Proof. 
  intros φ ψ w. rewrite forces_Impl. intro HboxImp.
  rewrite forces_Impl. intro Hboxφ.
  rewrite forces_Box in HboxImp. rewrite forces_Box in Hboxφ. rewrite forces_Box.
  intros u Hwu.
  specialize (HboxImp u Hwu). rewrite forces_Impl in HboxImp.
  specialize (Hboxφ u Hwu).
  exact (HboxImp Hboxφ). 
Qed.

Theorem provable_K : forall φ ψ, Prov (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
Proof. 
  intros φ ψ. apply completeness_from_truth. 
  intro w. apply valid_K. 
Qed.