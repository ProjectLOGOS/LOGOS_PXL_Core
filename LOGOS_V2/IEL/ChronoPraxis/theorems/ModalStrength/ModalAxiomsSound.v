From Coq Require Import Program Setoids.Setoid.

Parameter form : Type.
Parameter can_world : Type.
Parameter can_R : can_world -> can_world -> Prop.
Parameter forces : can_world -> form -> Prop.
Parameter Prov : form -> Prop.

(* Modal operators over Prop *)
Parameter Box : form -> form.
Parameter Dia : form -> form.
Parameter Impl : form -> form -> form.

(* Modal operator capabilities *)
Class Cap_ForcesBox (W:Type) (R:W->W->Prop) (forces: W->form->Prop) : Prop :=
  { forces_box : forall w φ, forces w (Box φ) <-> (forall u, R w u -> forces u φ) }.

Class Cap_ForcesDia (W:Type) (R:W->W->Prop) (forces: W->form->Prop) : Prop :=
  { forces_dia : forall w φ, forces w (Dia φ) <-> (exists u, R w u /\ forces u φ) }.

Class Cap_ForcesImpl (W:Type) (R:W->W->Prop) (forces: W->form->Prop) : Prop :=
  { forces_impl : forall w φ ψ, forces w (Impl φ ψ) <-> (forces w φ -> forces w ψ) }.

Axiom forces_Box : forall w φ, forces w (Box φ) <-> (forall u, can_R w u -> forces u φ).
Axiom forces_Dia : forall w φ, forces w (Dia φ) <-> (exists u, can_R w u /\ forces u φ).
Axiom forces_Impl : forall w φ ψ, forces w (Impl φ ψ) <-> (forces w φ -> forces w ψ).

(* Semantic definition of Box and Dia - replaced by instances *)
Global Instance CapForcesBox_param : Cap_ForcesBox can_world can_R forces :=
  { forces_box := forces_Box }.

Global Instance CapForcesDia_param : Cap_ForcesDia can_world can_R forces :=
  { forces_dia := forces_Dia }.

Global Instance CapForcesImpl_param : Cap_ForcesImpl can_world can_R forces :=
  { forces_impl := forces_Impl }.

Parameter completeness_from_truth : forall φ, (forall w, forces w φ) -> Prov φ.

(* Frame classes from S4/S5 overlays *)
Module S4.
  Class Reflexive : Prop := reflexive_R :
    forall (w: can_world), can_R w w.
  Class Transitive : Prop := transitive_R :
    forall (w u v: can_world), can_R w u -> can_R u v -> can_R w v.
End S4.

Module S5.
  Class Reflexive : Prop := reflexive_R :
    forall (w: can_world), can_R w w.
  Class Symmetric : Prop := symmetric_R :
    forall (w u: can_world), can_R w u -> can_R u w.
  Class Transitive : Prop := transitive_R :
    forall (w u v: can_world), can_R w u -> can_R u v -> can_R w v.
End S5.

Set Implicit Arguments.

Section S4Sound.
  Context (Hrefl : S4.Reflexive) (Htran : S4.Transitive).

  (* T: □φ → φ is valid on reflexive frames *)
  Lemma valid_T `{Cap_ForcesBox can_world can_R forces} `{Cap_ForcesImpl can_world can_R forces} : forall (φ:form) (w:can_world), forces w (Impl (Box φ) φ).
  Proof.
    intros φ w. rewrite forces_impl. intro Hbox.
    rewrite forces_box in Hbox.
    (* Use reflexivity: R w w *)
    assert (Hww : can_R w w).
    { apply S4.reflexive_R. }
    specialize (Hbox w Hww).
    exact Hbox.
  Qed.

  (* 4: □φ → □□φ is valid on transitive frames *)
  Lemma valid_4 `{Cap_ForcesBox can_world can_R forces} `{Cap_ForcesImpl can_world can_R forces} : forall (φ:form) (w:can_world), forces w (Impl (Box φ) (Box (Box φ))).
  Proof.
    intros φ w. rewrite forces_impl. intro Hbox.
    rewrite forces_box in Hbox. rewrite forces_box.
    intros u Hwu. rewrite forces_box.
    intros v Huv.
    (* From w⊢□φ and R w u and R u v, transitivity gives R w v, so φ holds at v *)
    pose proof (S4.transitive_R w u v Hwu Huv) as Hwv.
    apply Hbox in Hwv. exact Hwv.
  Qed.

  Theorem provable_T `{Cap_ForcesBox can_world can_R forces} `{Cap_ForcesImpl can_world can_R forces} : forall φ, Prov (Impl (Box φ) φ).
  Proof.
    intro φ. apply completeness_from_truth. intro w. apply valid_T.
  Qed.

  Theorem provable_4 `{Cap_ForcesBox can_world can_R forces} `{Cap_ForcesImpl can_world can_R forces} : forall φ, Prov (Impl (Box φ) (Box (Box φ))).
  Proof.
    intro φ. apply completeness_from_truth. intro w. apply valid_4.
  Qed.
End S4Sound.

Section S5Sound.
  Context (Hrefl : S5.Reflexive) (Hsym : S5.Symmetric) (Htran : S5.Transitive).

  (* Inherit T and 4 from S4 *)
  Lemma valid_T_S5 `{Cap_ForcesBox can_world can_R forces} `{Cap_ForcesImpl can_world can_R forces} : forall (φ:form) (w:can_world), forces w (Impl (Box φ) φ).
  Proof.
    intros φ w. rewrite forces_impl. intro Hbox.
    rewrite forces_box in Hbox.
    (* Use reflexivity: R w w *)
    pose proof (S5.reflexive_R w) as Hww.
    specialize (Hbox w Hww).
    exact Hbox.
  Qed.

  Lemma valid_4_S5 `{Cap_ForcesBox can_world can_R forces} `{Cap_ForcesImpl can_world can_R forces} : forall (φ:form) (w:can_world), forces w (Impl (Box φ) (Box (Box φ))).
  Proof.
    intros φ w. rewrite forces_impl. intro Hbox.
    rewrite forces_box in Hbox. rewrite forces_box.
    intros u Hwu. rewrite forces_box.
    intros v Huv.
    (* From w⊢□φ and R w u and R u v, transitivity gives R w v, so φ holds at v *)
    pose proof (S5.transitive_R w u v Hwu Huv) as Hwv.
    apply Hbox in Hwv. exact Hwv.
  Qed.

  (* 5: ◇φ → □◇φ is valid on equivalence (S5) frames *)
  Lemma valid_5 `{Cap_ForcesBox can_world can_R forces} `{Cap_ForcesDia can_world can_R forces} `{Cap_ForcesImpl can_world can_R forces} : forall (φ:form) (w:can_world), forces w (Impl (Dia φ) (Box (Dia φ))).
  Proof.
    intros φ w. rewrite forces_impl. intro Hdia.
    rewrite forces_dia in Hdia. rewrite forces_box.
    intros v Hwv. rewrite forces_dia.
    (* From ◇φ at w: ∃u. R w u ∧ φ at u *)
    destruct Hdia as [u [Hwu Hφu]].
    (* From R w v and symmetry get R v w; combine with R w u to get R v u by transitivity; witness u *)
    pose proof (S5.symmetric_R w v Hwv) as Hvw.
    pose proof (S5.transitive_R v w u Hvw Hwu) as Hvu.
    exists u. split; [exact Hvu | exact Hφu].
  Qed.

  Theorem provable_T_S5 `{Cap_ForcesBox can_world can_R forces} `{Cap_ForcesImpl can_world can_R forces} : forall φ, Prov (Impl (Box φ) φ).
  Proof.
    intro φ. apply completeness_from_truth. intro w. apply valid_T_S5.
  Qed.

  Theorem provable_4_S5 `{Cap_ForcesBox can_world can_R forces} `{Cap_ForcesImpl can_world can_R forces} : forall φ, Prov (Impl (Box φ) (Box (Box φ))).
  Proof.
    intro φ. apply completeness_from_truth. intro w. apply valid_4_S5.
  Qed.

  Theorem provable_5 `{Cap_ForcesBox can_world can_R forces} `{Cap_ForcesDia can_world can_R forces} `{Cap_ForcesImpl can_world can_R forces} : forall φ, Prov (Impl (Dia φ) (Box (Dia φ))).
  Proof.
    intro φ. apply completeness_from_truth. intro w. apply valid_5.
  Qed.
End S5Sound.

(* Alternative Brouwer axiom B: φ → □◇φ (also valid in S5) *)
Section BrouwerAxiom.
  Context (Hrefl : S5.Reflexive) (Hsym : S5.Symmetric) (Htran : S5.Transitive).

  Lemma valid_B `{Cap_ForcesBox can_world can_R forces} `{Cap_ForcesDia can_world can_R forces} `{Cap_ForcesImpl can_world can_R forces} : forall (φ:form) (w:can_world), forces w (Impl φ (Box (Dia φ))).
  Proof.
    intros φ w. rewrite forces_impl. intro Hφ.
    rewrite forces_box. intros v Hwv.
    rewrite forces_dia.
    (* Use symmetry to get R v w, then witness w for the diamond *)
    pose proof (S5.symmetric_R w v Hwv) as Hvw.
    exists w. split; [exact Hvw | exact Hφ].
  Qed.

  Theorem provable_B `{Cap_ForcesBox can_world can_R forces} `{Cap_ForcesDia can_world can_R forces} `{Cap_ForcesImpl can_world can_R forces} : forall φ, Prov (Impl φ (Box (Dia φ))).
  Proof.
    intro φ. apply completeness_from_truth. intro w. apply valid_B.
  Qed.
End BrouwerAxiom.
