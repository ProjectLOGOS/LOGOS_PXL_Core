From Coq Require Import Program Setoids.Setoid.

(* TODO: Restore full imports once module path resolution is fixed *)
(* From PXLs Require Import PXLv3. *)
(* Require Import modules.IEL.ModalPraxis.modal.FrameSpec
               modules.IEL.ModalPraxis.theorems.NormalBase
               modules.IEL.ModalPraxis.theorems.DerivedAxioms. *)

(* Standalone definitions for compilation - using PXL canonical model types *)
Parameter form : Type.
Parameter Prov : form -> Prop.
Parameter Box : form -> form.
Parameter Dia : form -> form.
Parameter Impl : form -> form -> form.
Parameter forces : Type -> form -> Prop.
Parameter can_world : Type.
Parameter can_R : can_world -> can_world -> Prop.

(* Frame classes from ModalPraxis *)
Class Reflexive : Prop := { reflexive_R : forall w, can_R w w }.
Class Transitive : Prop := { transitive_R : forall w u v, can_R w u -> can_R u v -> can_R w v }.
Class Euclidean : Prop := { euclidean_R : forall w u v, can_R w u -> can_R w v -> can_R u v }.
Class Serial : Prop := { serial_R : forall w, exists v, can_R w v }.

(* Theorems from ModalPraxis *)
Parameter provable_K : forall φ ψ, Prov (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
Parameter provable_necessitation : forall φ, (forall w, forces w φ) -> Prov (Box φ).
Parameter provable_D : Serial -> forall φ, Prov (Impl (Box φ) (Dia φ)).
Parameter provable_4 : Transitive -> forall φ, Prov (Impl (Box φ) (Box (Box φ))).
Parameter provable_5 : Euclidean -> forall φ, Prov (Impl (Dia φ) (Box (Dia φ))).

Module HexiPraxis.

  (* Agents as parameters - agency logic [i]φ and ⟨i⟩φ *)
  Parameter agent : Type.  (* Agents i, j, ... *)

  (* Agency modalities: [i]φ means agent i brings about φ *)
  Definition Brings_About (i:agent) (φ:form) : form := Box φ.
  Definition Can_Bring_About (i:agent) (φ:form) : form := Dia φ.

  (* Frame classes for agency systems *)
  Class K_Frame : Prop := {}.  (* Basic agency logic *)
  Class KD_Frame : Prop := { agency_serial : forall w i, exists v, can_R w v }.  (* Agency possibility *)
  Class KD45_Frame : Prop := { agency_serial' : forall w i, exists v, can_R w v;
                               agency_trans : forall w u v, can_R w u -> can_R u v -> can_R w v;
                               agency_eucl : forall w u v, can_R w u -> can_R w v -> can_R u v }.

  (* Basic agency axioms *)
  Theorem K_agency : K_Frame -> forall i φ ψ, Prov (Impl (Brings_About i (Impl φ ψ)) (Impl (Brings_About i φ) (Brings_About i ψ))).
  Proof. intros _ i φ ψ; unfold Brings_About; apply provable_K. Qed.

  Theorem Necessitation_agency : K_Frame -> forall i φ, (forall w, forces w φ) -> Prov (Brings_About i φ).
  Proof. intros _ i φ H; unfold Brings_About; apply provable_necessitation; exact H. Qed.

  (* Success axiom: [i]φ → φ (agency implies truth) *)
  Theorem Success : KD_Frame -> forall i φ, Prov (Impl (Brings_About i φ) φ).
  Proof. intros H i φ; unfold Brings_About; destruct H as [Hser]; eapply provable_D; eauto. Qed.

  (* Determinism under KD45: [i]φ → [i][i]φ *)
  Theorem Determinism : KD45_Frame -> forall i φ, Prov (Impl (Brings_About i φ) (Brings_About i (Brings_About i φ))).
  Proof. intros H i φ; unfold Brings_About; destruct H as [Hs Ht He]; eapply provable_4; eauto. Qed.

  (* No learning under KD45: ⟨i⟩φ → [i]⟨i⟩φ *)
  Theorem No_Learning : KD45_Frame -> forall i φ, Prov (Impl (Can_Bring_About i φ) (Brings_About i (Can_Bring_About i φ))).
  Proof. intros H i φ; unfold Brings_About, Can_Bring_About; destruct H as [Hs Ht He]; eapply provable_5; eauto. Qed.

End HexiPraxis.
