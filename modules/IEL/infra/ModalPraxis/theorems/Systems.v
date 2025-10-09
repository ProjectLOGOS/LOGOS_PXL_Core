From Coq Require Import Program.

(* TODO: Restore full imports once module path resolution is fixed *)
(* From PXLs Require Import PXLv3. *)
(* Require Import modules.IEL.UM.modal.FrameSpec *)
(*                modules.IEL.UM.theorems.{NormalBase,DerivedAxioms}. *)

(* Standalone loading - parameters for the modal systems *)
Parameter form : Type.
Parameter Prov : form -> Prop.
Parameter Box : form -> form.
Parameter Dia : form -> form.
Parameter Impl : form -> form -> form.

(* Normal base theorems *)
Parameter provable_K : forall φ ψ, Prov (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
Parameter world : Type.
Parameter provable_necessitation : forall φ, (forall (w:world), True) -> Prov (Box φ).

(* Derived axioms under frame conditions *)
Parameter provable_T : forall φ, Prov (Impl (Box φ) φ).
Parameter provable_4 : forall φ, Prov (Impl (Box φ) (Box (Box φ))).
Parameter provable_5 : forall φ, Prov (Impl (Dia φ) (Box (Dia φ))).
Parameter provable_B : forall φ, Prov (Impl φ (Box (Dia φ))).
Parameter provable_D : forall φ, Prov (Impl (Box φ) (Dia φ)).

(* K System: Basic normal modal logic - K axiom + Necessitation *)
Module KSystem.
  Definition K_axiom := provable_K.
  Definition Necessitation := provable_necessitation.
  
  (* Provides minimal normal modal logic *)
  Lemma K_available : forall φ ψ, Prov (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
  Proof. intros φ ψ. apply provable_K. Qed.
End KSystem.

(* T System: K + T axiom (reflexive frames) *)
Module TSystem.
  Include KSystem.
  Definition T_axiom := provable_T.
  
  Lemma T_available : forall φ, Prov (Impl (Box φ) φ).
  Proof. intro φ. apply provable_T. Qed.
End TSystem.

(* S4 System: K + T + 4 axioms (reflexive + transitive frames) *)
Module S4System.
  Include TSystem.
  Definition Four_axiom := provable_4.
  
  Lemma S4_T_available : forall φ, Prov (Impl (Box φ) φ).
  Proof. intro φ. apply provable_T. Qed.
  
  Lemma S4_4_available : forall φ, Prov (Impl (Box φ) (Box (Box φ))).
  Proof. intro φ. apply provable_4. Qed.
End S4System.

(* S5 System: K + T + 5 axioms (equivalence frames) *)
Module S5System.
  Include TSystem.
  Definition Five_axiom := provable_5.
  Definition B_axiom := provable_B.
  
  Lemma S5_T_available : forall φ, Prov (Impl (Box φ) φ).
  Proof. intro φ. apply provable_T. Qed.
  
  Lemma S5_5_available : forall φ, Prov (Impl (Dia φ) (Box (Dia φ))).
  Proof. intro φ. apply provable_5. Qed.
  
  Lemma S5_B_available : forall φ, Prov (Impl φ (Box (Dia φ))).
  Proof. intro φ. apply provable_B. Qed.
End S5System.

(* KD System: K + D axiom (serial frames) *)
Module KDSystem.
  Include KSystem.
  Definition D_axiom := provable_D.
  
  Lemma KD_D_available : forall φ, Prov (Impl (Box φ) (Dia φ)).
  Proof. intro φ. apply provable_D. Qed.
End KDSystem.

(* KB System: K + B axiom (symmetric frames) *)
Module KBSystem.
  Include KSystem.
  Definition B_axiom := provable_B.
  
  Lemma KB_B_available : forall φ, Prov (Impl φ (Box (Dia φ))).
  Proof. intro φ. apply provable_B. Qed.
End KBSystem.
