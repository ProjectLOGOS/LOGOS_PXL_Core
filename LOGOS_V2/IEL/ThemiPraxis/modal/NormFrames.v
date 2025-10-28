From Coq Require Import Program Setoids.Setoid.

(* TODO: Restore full imports once module path resolution is fixed *)
(* From PXLs Require Import PXLv3. *)
(* Require Import modules.Internal Emergent Logics.ModalPraxis.modal.FrameSpec
               modules.Internal Emergent Logics.ModalPraxis.theorems.NormalBase
               modules.Internal Emergent Logics.ModalPraxis.theorems.DerivedAxioms. *)

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

Set Implicit Arguments.

Module ThemiPraxis.

  (* Worlds already provided by kernel; we use modal □ as "Obligatory". *)
  Definition O (φ:form) : form := Box φ.
  Definition P (φ:form) : form := Dia φ.  (* Permitted *)

  (* Frame classes for deontic systems *)
  Class K_Frame  : Prop := {}.                         (* base normal *)
  Class KD_Frame : Prop := { kd_serial : Serial }.     (* D: Oφ → Pφ *)
  Class KD45_Frame : Prop := { kd_serial' : Serial; kd_trans : Transitive; kd_eucl : Euclidean }.

  (* Base normal rules *)
  Theorem K_axiom : K_Frame -> forall φ ψ, Prov (Impl (O (Impl φ ψ)) (Impl (O φ) (O ψ))).
  Proof. intros _ φ ψ; change (Prov (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ)))); apply provable_K. Qed.

  Theorem Necessitation : K_Frame -> forall φ, (forall w, forces w φ) -> Prov (O φ).
  Proof. intros _ φ H; change (Prov (Box φ)); apply provable_necessitation; exact H. Qed.

  (* D: seriality *)
  Theorem D_axiom : KD_Frame -> forall φ, Prov (Impl (O φ) (P φ)).
  Proof. intros H φ; destruct H as [Hser]; change (Prov (Impl (Box φ) (Dia φ))); eapply provable_D; eauto. Qed.

  (* 4 and 5 under KD45; standard KD45 deontic *)
  Theorem Four_axiom : KD45_Frame -> forall φ, Prov (Impl (O φ) (O (O φ))).
  Proof. intros H φ; destruct H as [Hs Ht He]; change (Prov (Impl (Box φ) (Box (Box φ)))); eapply provable_4; eauto. Qed.

  Theorem Five_axiom : KD45_Frame -> forall φ, Prov (Impl (P φ) (O (P φ))).
  Proof. intros H φ; destruct H as [Hs Ht He]; change (Prov (Impl (Dia φ) (Box (Dia φ)))); eapply provable_5; eauto. Qed.

End ThemiPraxis.
