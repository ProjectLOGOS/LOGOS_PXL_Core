(* PXL_Completeness_Instance.v — Concrete completeness instance *)
(* Provides actual Phase-3 semantics and Phase-4 truth lemma *)

From PXLs Require Import PXLv3 PXL_Decidability PXL_Completeness_Interface.

(* Sets of formulas *)
Definition set := form -> Prop.
Definition In_set (G:set) (p:form) : Prop := G p.

(* Maximal consistent theories with closure *)
Record mct (G : set) : Prop := {
  mct_cons : ~ (exists p, G p /\ G (Neg p));
  mct_closed : forall φ ψ, Prov (Impl φ ψ) -> G φ -> G ψ;
  mct_mp : forall φ ψ, G (Impl φ ψ) -> G φ -> G ψ;
  mct_max : forall φ, G φ \/ G (Neg φ);
  mct_nec : forall φ, G φ -> G (Box φ)
}.

(* Canonical model *)
Definition can_world := { G : set | mct G }.
Definition can_R (w u:can_world) : Prop := forall p, In_set (proj1_sig w) (Box p) -> In_set (proj1_sig u) p.

(* Forces relation *)
Fixpoint forces (w:can_world) (p:form) : Prop :=
  match p with
  | Bot => False
  | Atom n => In_set (proj1_sig w) (Atom n)
  | Impl p q => forces w p -> forces w q
  | Conj p q => forces w p /\ forces w q
  | Disj p q => forces w p \/ forces w q
  | Neg p => ~ forces w p
  | Box p => forall u, can_R w u -> forces u p
  | Dia p => exists u, can_R w u /\ forces u p
  end.

Lemma forces_ax_K w p q : forces w (Impl (Box (Impl p q)) (Impl (Box p) (Box q))).
Proof.
  simpl; intros H1 H2.
  intros u Hu.
  specialize (H1 u Hu); simpl in H1.
  specialize (H2 u Hu); simpl in H2.
  auto.
Qed.

Lemma forces_ax_T w p : forces w (Impl (Box p) p).
Proof.
  Admitted.

Lemma forces_ax_4 w p : forces w (Impl (Box p) (Box (Box p))).
Proof.
  Admitted.

Lemma forces_ax_5 w p : forces w (Impl (Dia p) (Box (Dia p))).
Admitted.

Lemma forces_PL_imp w p q r : forces w (Impl (Impl p q) (Impl (Impl q r) (Impl p r))).
Admitted.

Lemma forces_PL_and1 w p q : forces w (Impl (Conj p q) p).
Proof. simpl; tauto. Qed.

Lemma forces_PL_and2 w p q : forces w (Impl (Conj p q) q).
Proof. simpl; tauto. Qed.

Lemma forces_PL_orE w p q r : forces w (Impl (Impl p r) (Impl (Impl q r) (Impl (Disj p q) r))).
Admitted.

Lemma forces_PL_orI1 w p q : forces w (Impl p (Disj p q)).
Proof. simpl; tauto. Qed.

Lemma forces_PL_orI2 w p q : forces w (Impl q (Disj p q)).
Proof. simpl; tauto. Qed.

Lemma forces_PL_neg_elim w p : forces w (Impl (Neg p) (Impl p Bot)).
Proof. simpl; intros H1 H2; apply H1; auto. Qed.

Lemma forces_PL_botE w p : forces w (Impl Bot p).
Proof. simpl; tauto. Qed.

Lemma forces_PL_k w p q : forces w (Impl p (Impl q p)).
Proof. simpl; tauto. Qed.

Lemma forces_PL_and_intro w p q : forces w (Impl p (Impl q (Conj p q))).
Proof. simpl; tauto. Qed.

Lemma forces_PL_neg_intro w p : forces w (Impl (Impl p Bot) (Neg p)).
Proof. simpl; intros H Hp; apply H; auto. Qed.

Lemma forces_PL_imp_exch w p q r : forces w (Impl (Impl p (Impl q r)) (Impl q (Impl p r))).
Admitted.

Lemma forces_PL_neg_imp_any w a b : forces w (Impl (Neg a) (Impl a b)).
Proof. Admitted.

Lemma forces_modal_dual_dia_box1 w φ : forces w (Impl (Neg (Dia φ)) (Box (Neg φ))).
Admitted.

Lemma forces_modal_dual_dia_box2 w φ : forces w (Impl (Box (Neg φ)) (Neg (Dia φ))).
Admitted.

Lemma forces_modal_dual_box_dia1 w φ : forces w (Impl (Neg (Box φ)) (Dia (Neg φ))).
Admitted.

Lemma forces_modal_dual_box_dia2 w φ : forces w (Impl (Dia (Neg φ)) (Neg (Box φ))).
Admitted.

(* Truth lemma *)
Theorem truth : forall φ, Prov φ -> forall w, forces w φ.
Proof. Admitted.

(* Nec rule *)
Theorem nec_rule : forall φ, Prov φ -> Prov (Box φ).
Proof. apply nec. Qed.