From Coq Require Import Program Setoids.Setoid.

(* TODO: Restore full imports once module path resolution is fixed *)
(* From PXLs Require Import PXLv3. *)
(* Require Import PXLs.IEL.Infra.theorems.ModalStrength.{S4Overlay,S5Overlay} *)
(*                modules.IEL.ModalPraxis.modal.FrameSpec *)
(*                modules.IEL.ModalPraxis.theorems.{NormalBase,DerivedAxioms}. *)

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
Class Serial     : Prop := serial_R     : forall w, exists u, can_R w u.
Class Reflexive  : Prop := reflexive_R  : forall w, can_R w w.
Class Symmetric  : Prop := symmetric_R  : forall w u, can_R w u -> can_R u w.
Class Transitive : Prop := transitive_R : forall w u v, can_R w u -> can_R u v -> can_R w v.
Class Euclidean  : Prop := euclid_R     : forall w u v, can_R w u -> can_R w v -> can_R u v.

(* UM-IEL theorems *)
Parameter provable_K : forall φ ψ, Prov (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
Parameter provable_necessitation : forall φ, (forall w, forces w φ) -> Prov (Box φ).
Parameter provable_T : forall (Hrefl: Reflexive) (Htran: Transitive) φ, Prov (Impl (Box φ) φ).
Parameter provable_4 : forall (Hrefl: Reflexive) (Htran: Transitive) φ, Prov (Impl (Box φ) (Box (Box φ))).
Parameter provable_B : forall (Hsym: Symmetric) (Htran: Transitive) (Hrefl: Reflexive) φ, Prov (Impl φ (Box (Dia φ))).
Parameter provable_5 : forall (Hsym: Symmetric) (Htran: Transitive) (Hrefl: Reflexive) φ, Prov (Impl (Dia φ) (Box (Dia φ))).

Set Implicit Arguments.

Module S4_As_UM.
  Section Inst.
    Context (Hrefl : S4.Reflexive) (Htran : S4.Transitive).
    
    (* Show UM-IEL flags available from CP overlays *)
    Definition UM_Reflexive : Reflexive := fun w => S4.reflexive_R w.
    Definition UM_Transitive : Transitive := fun w u v => S4.transitive_R w u v.
    
    (* Equivalences of schemata: reuse UM-IEL provables under flags *)
    Theorem T_eq : forall φ, Prov (Impl (Box φ) φ).
    Proof. intro φ. apply (provable_T UM_Reflexive UM_Transitive φ). Qed.
    
    Theorem Four_eq : forall φ, Prov (Impl (Box φ) (Box (Box φ))).
    Proof. intro φ. apply (provable_4 UM_Reflexive UM_Transitive φ). Qed.
    
    Theorem K_eq : forall φ ψ, Prov (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
    Proof. intros φ ψ. apply provable_K. Qed.
    
    Theorem Nec_eq : forall φ, (forall w, forces w φ) -> Prov (Box φ).
    Proof. intros φ H. apply provable_necessitation. exact H. Qed.
  End Inst.
End S4_As_UM.

Module S5_As_UM.
  Section Inst.
    Context (Hrefl : S5.Reflexive) (Hsym : S5.Symmetric) (Htran : S5.Transitive).
    
    Definition UM_Reflexive : Reflexive := fun w => S5.reflexive_R w.
    Definition UM_Symmetric : Symmetric := fun w u => S5.symmetric_R w u.
    Definition UM_Transitive : Transitive := fun w u v => S5.transitive_R w u v.
    
    Theorem B_eq : forall φ, Prov (Impl φ (Box (Dia φ))).
    Proof. intro φ. apply (provable_B UM_Symmetric UM_Transitive UM_Reflexive φ). Qed.
    
    Theorem Five_eq : forall φ, Prov (Impl (Dia φ) (Box (Dia φ))).
    Proof. intro φ. apply (provable_5 UM_Symmetric UM_Transitive UM_Reflexive φ). Qed.
    
    Theorem T_eq : forall φ, Prov (Impl (Box φ) φ).
    Proof. intro φ. apply (provable_T UM_Reflexive UM_Transitive φ). Qed.
    
    Theorem Four_eq : forall φ, Prov (Impl (Box φ) (Box (Box φ))).
    Proof. intro φ. apply (provable_4 UM_Reflexive UM_Transitive φ). Qed.
    
    Theorem K_eq : forall φ ψ, Prov (Impl (Box (Impl φ ψ)) (Impl (Box φ) (Box ψ))).
    Proof. intros φ ψ. apply provable_K. Qed.
    
    Theorem Nec_eq : forall φ, (forall w, forces w φ) -> Prov (Box φ).
    Proof. intros φ H. apply provable_necessitation. exact H. Qed.
  End Inst.
End S5_As_UM.
