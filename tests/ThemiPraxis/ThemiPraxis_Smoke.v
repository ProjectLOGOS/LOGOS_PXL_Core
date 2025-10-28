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

Module ThemiPraxis.

  (* Worlds already provided by kernel; we use modal ? as "Obligatory". *)
  Definition O (f:form) : form := Box f.
  Definition P (f:form) : form := Dia f.  (* Permitted *)

  (* Frame classes for deontic systems *)
  Class K_Frame  : Prop := {}.                         (* base normal *)
  Class KD_Frame : Prop := { kd_serial : Serial }.     (* D: Of ? Pf *)
  Class KD45_Frame : Prop := { kd_serial' : Serial; kd_trans : Transitive; kd_eucl : Euclidean }.

  (* Base normal rules *)
  Theorem K_axiom : K_Frame -> forall f g, Prov (Impl (O (Impl f g)) (Impl (O f) (O g))).
  Proof. intros _ f g; change (Prov (Impl (Box (Impl f g)) (Impl (Box f) (Box g)))); apply provable_K. Qed.

  Theorem Necessitation : K_Frame -> forall f, (forall w, forces w f) -> Prov (O f).
  Proof. intros _ f H; change (Prov (Box f)); apply provable_necessitation; exact H. Qed.

  (* D: seriality *)
  Theorem D_axiom : KD_Frame -> forall f, Prov (Impl (O f) (P f)).
  Proof. intros H f; destruct H as [Hser]; change (Prov (Impl (Box f) (Dia f))); eapply provable_D; eauto. Qed.

  (* 4 and 5 under KD45; standard KD45 deontic *)
  Theorem Four_axiom : KD45_Frame -> forall f, Prov (Impl (O f) (O (O f))).
  Proof. intros H f; destruct H as [Hs Ht He]; change (Prov (Impl (Box f) (Box (Box f)))); eapply provable_4; eauto. Qed.

  Theorem Five_axiom : KD45_Frame -> forall f, Prov (Impl (P f) (O (P f))).
  Proof. intros H f; destruct H as [Hs Ht He]; change (Prov (Impl (Dia f) (Box (Dia f)))); eapply provable_5; eauto. Qed.

End ThemiPraxis.

Module T.
  Import ThemiPraxis.
  Lemma k_ok  : K_Frame  -> forall f g, Prov (Impl (O (Impl f g)) (Impl (O f) (O g))).
  Proof. apply K_axiom. Qed.
  Lemma d_ok  : KD_Frame -> forall f, Prov (Impl (O f) (P f)).
  Proof. apply D_axiom. Qed.
  Lemma d45_4_ok : KD45_Frame -> forall f, Prov (Impl (O f) (O (O f))).
  Proof. apply Four_axiom. Qed.
  Lemma d45_5_ok : KD45_Frame -> forall f, Prov (Impl (P f) (O (P f))).
  Proof. apply Five_axiom. Qed.
End T.
