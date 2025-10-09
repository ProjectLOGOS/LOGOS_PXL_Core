From Coq Require Import Program Setoids.Setoid.

(* TODO: Restore full imports once module path resolution is fixed *)
(* From PXLs Require Import PXLv3. *)
(* Require Import modules.chronopraxis.theorems.ModalStrength.{S4Overlay,S5Overlay} *)
(*                modules.IEL.ModalPraxis.modal.FrameSpec *)
(*                modules.IEL.ModalPraxis.theorems.{NormalBase,DerivedAxioms} *)
(*                modules.IEL.ChronoPraxis.theorems.ModalStrength.UMAdapters. *)

(* Standalone loading for compilation *)
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

(* ChronoPraxis S4/S5 frame classes *)
Module S4.
  Class Reflexive : Prop := reflexive_R : forall w, can_R w w.
  Class Transitive : Prop := transitive_R : forall w u v, can_R w u -> can_R u v -> can_R w v.
End S4.

Module S5.
  Class Reflexive : Prop := reflexive_R : forall w, can_R w w.
  Class Symmetric : Prop := symmetric_R : forall w u, can_R w u -> can_R u w.
  Class Transitive : Prop := transitive_R : forall w u v, can_R w u -> can_R u v -> can_R w v.
End S5.

(* UM-IEL frame classes *)
Class Reflexive  : Prop := reflexive_R  : forall w, can_R w w.
Class Symmetric  : Prop := symmetric_R  : forall w u, can_R w u -> can_R u w.
Class Transitive : Prop := transitive_R : forall w u v, can_R w u -> can_R u v -> can_R w v.

(* UM-IEL theorems *)
Parameter provable_K : forall φ ψ, Prov (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
Parameter provable_necessitation : forall φ, (forall w, forces w φ) -> Prov (Box φ).
Parameter provable_T : forall (Hrefl: Reflexive) (Htran: Transitive) φ, Prov (Impl (Box φ) φ).
Parameter provable_4 : forall (Hrefl: Reflexive) (Htran: Transitive) φ, Prov (Impl (Box φ) (Box (Box φ))).
Parameter provable_B : forall (Hsym: Symmetric) (Htran: Transitive) (Hrefl: Reflexive) φ, Prov (Impl φ (Box (Dia φ))).
Parameter provable_5 : forall (Hsym: Symmetric) (Htran: Transitive) (Hrefl: Reflexive) φ, Prov (Impl (Dia φ) (Box (Dia φ))).

Set Implicit Arguments.

Section S4_Equiv.
  Context (Hrefl : S4.Reflexive) (Htran : S4.Transitive).

  (* Convert CP overlay frame properties to UM-IEL frame classes *)
  Definition S4_UM_Reflexive : Reflexive := fun w => S4.reflexive_R w.
  Definition S4_UM_Transitive : Transitive := fun w u v => S4.transitive_R w u v.

  (* CP overlay provided: S4.conservative_nonmodal etc. We prove CP's T/4 equal UM's T/4. *)
  Theorem S4_T_from_ModalPraxis : forall φ, Prov (Impl (Box φ) φ).
  Proof. intro φ. apply (provable_T S4_UM_Reflexive S4_UM_Transitive). Qed.
  
  Theorem S4_4_from_ModalPraxis : forall φ, Prov (Impl (Box φ) (Box (Box φ))).
  Proof. intro φ. apply (provable_4 S4_UM_Reflexive S4_UM_Transitive). Qed.
  
  Theorem S4_K_from_ModalPraxis : forall φ ψ, Prov (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
  Proof. intros φ ψ. apply provable_K. Qed.
  
  Theorem S4_Nec_from_ModalPraxis : forall φ, (forall w, forces w φ) -> Prov (Box φ).
  Proof. intros φ H. apply provable_necessitation. exact H. Qed.
End S4_Equiv.

Section S5_Equiv.
  Context (Hrefl : S5.Reflexive) (Hsym : S5.Symmetric) (Htran : S5.Transitive).
  
  (* Convert CP overlay frame properties to UM-IEL frame classes *)
  Definition S5_UM_Reflexive : Reflexive := fun w => S5.reflexive_R w.
  Definition S5_UM_Symmetric : Symmetric := fun w u => S5.symmetric_R w u.
  Definition S5_UM_Transitive : Transitive := fun w u v => S5.transitive_R w u v.
  
  Theorem S5_B_from_ModalPraxis : forall φ, Prov (Impl φ (Box (Dia φ))).
  Proof. intro φ. apply (provable_B S5_UM_Symmetric S5_UM_Transitive S5_UM_Reflexive). Qed.
  
  Theorem S5_5_from_ModalPraxis : forall φ, Prov (Impl (Dia φ) (Box (Dia φ))).
  Proof. intro φ. apply (provable_5 S5_UM_Symmetric S5_UM_Transitive S5_UM_Reflexive). Qed.
  
  Theorem S5_T_from_ModalPraxis : forall φ, Prov (Impl (Box φ) φ).
  Proof. intro φ. apply (provable_T S5_UM_Reflexive S5_UM_Transitive). Qed.
  
  Theorem S5_4_from_ModalPraxis : forall φ, Prov (Impl (Box φ) (Box (Box φ))).
  Proof. intro φ. apply (provable_4 S5_UM_Reflexive S5_UM_Transitive). Qed.
  
  Theorem S5_K_from_ModalPraxis : forall φ ψ, Prov (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
  Proof. intros φ ψ. apply provable_K. Qed.
  
  Theorem S5_Nec_from_ModalPraxis : forall φ, (forall w, forces w φ) -> Prov (Box φ).
  Proof. intros φ H. apply provable_necessitation. exact H. Qed.
End S5_Equiv.