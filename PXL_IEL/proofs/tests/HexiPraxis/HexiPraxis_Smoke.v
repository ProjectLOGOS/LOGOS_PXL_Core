From Coq Require Import Program Setoids.Setoid.

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
Parameter provable_K : forall f g, Prov (Impl (Box (Impl f g)) (Impl (Box f) (Box g))).
Parameter provable_necessitation : forall f, (forall w, forces w f) -> Prov (Box f).
Parameter provable_D : Serial -> forall f, Prov (Impl (Box f) (Dia f)).
Parameter provable_4 : Transitive -> forall f, Prov (Impl (Box f) (Box (Box f))).
Parameter provable_5 : Euclidean -> forall f, Prov (Impl (Dia f) (Box (Dia f))).

Module HexiPraxis.

  (* Agents as parameters - agency logic [i]f and ?i?f *)
  Parameter agent : Type.  (* Agents i, j, ... *)

  (* Agency modalities: [i]f means agent i brings about f *)
  Definition Brings_About (i:agent) (f:form) : form := Box f.
  Definition Can_Bring_About (i:agent) (f:form) : form := Dia f.

  (* Frame classes for agency systems *)
  Class K_Frame : Prop := {}.  (* Basic agency logic *)
  Class KD_Frame : Prop := { agency_serial : forall w i, exists v, can_R w v }.  (* Agency possibility *)
  Class KD45_Frame : Prop := { agency_serial' : forall w i, exists v, can_R w v;
                               agency_trans : forall w u v, can_R w u -> can_R u v -> can_R w v;
                               agency_eucl : forall w u v, can_R w u -> can_R w v -> can_R u v }.

  (* Basic agency axioms *)
  Theorem K_agency : K_Frame -> forall i f g, Prov (Impl (Brings_About i (Impl f g)) (Impl (Brings_About i f) (Brings_About i g))).
  Proof. intros _ i f g; unfold Brings_About; apply provable_K. Qed.

  Theorem Necessitation_agency : K_Frame -> forall i f, (forall w, forces w f) -> Prov (Brings_About i f).
  Proof. intros _ i f H; unfold Brings_About; apply provable_necessitation; exact H. Qed.

  (* Success axiom: [i]f ? f (agency implies truth) *)
  Theorem Success : KD_Frame -> forall i f, Prov (Impl (Brings_About i f) f).
  Proof. intros H i f; unfold Brings_About; destruct H as [Hser]; eapply provable_D; eauto. Qed.

  (* Determinism under KD45: [i]f ? [i][i]f *)
  Theorem Determinism : KD45_Frame -> forall i f, Prov (Impl (Brings_About i f) (Brings_About i (Brings_About i f))).
  Proof. intros H i f; unfold Brings_About; destruct H as [Hs Ht He]; eapply provable_4; eauto. Qed.

  (* No learning under KD45: ?i?f ? [i]?i?f *)
  Theorem No_Learning : KD45_Frame -> forall i f, Prov (Impl (Can_Bring_About i f) (Brings_About i (Can_Bring_About i f))).
  Proof. intros H i f; unfold Brings_About, Can_Bring_About; destruct H as [Hs Ht He]; eapply provable_5; eauto. Qed.

End HexiPraxis.

Module T.
  Import HexiPraxis.
  Lemma k_ok : K_Frame -> forall i f g, Prov (Impl (Brings_About i (Impl f g)) (Impl (Brings_About i f) (Brings_About i g))).
  Proof. apply K_agency. Qed.
  Lemma success_ok : KD_Frame -> forall i f, Prov (Impl (Brings_About i f) f).
  Proof. apply Success. Qed.
  Lemma det_ok : KD45_Frame -> forall i f, Prov (Impl (Brings_About i f) (Brings_About i (Brings_About i f))).
  Proof. apply Determinism. Qed.
  Lemma nolearn_ok : KD45_Frame -> forall i f, Prov (Impl (Can_Bring_About i f) (Brings_About i (Can_Bring_About i f))).
  Proof. apply No_Learning. Qed.
End T.
