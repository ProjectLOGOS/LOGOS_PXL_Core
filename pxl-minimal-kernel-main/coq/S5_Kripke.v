From Coq Require Import Logic.Classical.

(*
  S5_Kripke.v
  Semantic S5 on Kripke frames with an equivalence accessibility.
  Modal propositions are predicates over worlds (W -> Prop).
  Box p w := forall w', R w w' -> p w'
  Dia p w := exists w', R w w' /\ p w'
  Explicit proofs only. UTF-8, no markdown fences.
*)

Section S5_Semantics.

Variable W : Type.
Variable R : W -> W -> Prop.

Hypothesis R_refl  : forall w, R w w.
Hypothesis R_symm  : forall w u, R w u -> R u w.
Hypothesis R_trans : forall w u v, R w u -> R u v -> R w v.

Definition box (p:W->Prop) : W->Prop := fun w => forall u, R w u -> p u.
Definition dia (p:W->Prop) : W->Prop := fun w => exists u, R w u /\ p u.

Lemma K_sem : forall p q, (forall w, box (fun x => p x -> q x) w -> (box p w -> box q w)).
Proof.
  intros p q w Himp Hbp u Hwu.
  apply (Himp u Hwu).
  apply (Hbp u Hwu).
Qed.

Lemma T_sem : forall p, forall w, box p w -> p w.
Proof.
  intros p w Hb. apply Hb. apply R_refl.
Qed.

Lemma Four_sem : forall p, forall w, box p w -> box (box p) w.
Proof.
  intros p w Hb u Hwu v Huv.
  apply Hb. eapply R_trans; eauto.
Qed.

Lemma Five_sem : forall p, forall w, dia p w -> box (dia p) w.
Proof.
  intros p w [u [Hwu Hpu]] v Hwv.
  exists u. split; [ | exact Hpu].
  (* In equivalence relations: from R w v and R w u derive R v u via symmetry+transitivity. *)
  apply R_trans with (u:=w).
  - apply R_symm. exact Hwv.
  - exact Hwu.
Qed.

Lemma dual_box_dia : forall p w, box p w <-> ~ dia (fun x => ~ p x) w.
Proof.
  intros p w. split.
  - intros Hb [u [Hwu Hnp]]. apply Hnp. apply Hb; assumption.
  - intros Hnot u Hwu. destruct (classic (p u)) as [Hp|Hn].
    + exact Hp.
    + exfalso. apply Hnot. exists u. split; [assumption| exact Hn].
Qed.

Lemma dual_dia_box : forall p w, dia p w <-> ~ box (fun x => ~ p x) w.
Proof.
  intros p w. split.
  - intros [u [Hwu Hpu]] Hb. apply (Hb u Hwu). exact Hpu.
  - intros Hnot. destruct (classic (exists u, R w u /\ p u)) as [Hex|Hno].
    + exact Hex.
    + exfalso. apply Hnot. intros u Hwu Hu.
      apply Hno. exists u. split; [assumption| exact Hu].
Qed.

Lemma mono_box : forall p q w, (forall x, p x -> q x) -> box p w -> box q w.
Proof.
  intros p q w Himp Hb u Hwu. apply Himp, Hb; assumption.
Qed.

Lemma mono_dia : forall p q w, (forall x, p x -> q x) -> dia p w -> dia q w.
Proof.
  intros p q w Himp [u [Hwu Hpu]]. exists u. split; [assumption| apply Himp; assumption].
Qed.

Lemma dist_box_and : forall p q w, box (fun x => p x /\ q x) w <-> (box p w /\ box q w).
Proof.
  intros p q w. split.
  - intros Hb. split; intros u Hwu.
    + destruct (Hb u Hwu) as [H1 H2]. apply H1.
    + destruct (Hb u Hwu) as [H1 H2]. apply H2.
  - intros [Hp Hq] u Hwu. split; [apply Hp | apply Hq]; assumption.
Qed.

Lemma dist_dia_or : forall p q w, dia (fun x => p x \/ q x) w <-> (dia p w \/ dia q w).
Proof.
  intros p q w. split.
  - intros [u [Hwu [Hp|Hq]]]; [left; exists u; split; assumption | right; exists u; split; assumption].
  - intros [[u [Hwu Hp]] | [u [Hwu Hq]]];
    [ exists u; split; [assumption | left; assumption ]
    | exists u; split; [assumption | right; assumption ] ].
Qed.

Lemma collapse_box : forall p w, box p w <-> box (box p) w.
Proof.
  intros p w. split.
  - intros Hb u Hwu v Huv. apply Hb. eapply R_trans; eauto.
  - intros Hbb. apply (Hbb w). apply R_refl.
Qed.

Lemma collapse_dia_box : forall p w, dia p w <-> box (dia p) w.
Proof.
  intros p w. split.
  - apply Five_sem.
  - intros Hbd. destruct (Hbd w (R_refl w)) as [u [Hwu Hpu]].
    exists u. split; assumption.
Qed.

Lemma collapse_box_dia : forall p w, box p w <-> dia (box p) w.
Proof.
  intros p w. split.
  - intros Hb. exists w. split; [apply R_refl|]. intros u Hwu. apply Hb. exact Hwu.
  - intros [u [Hwu Hbp]] v Hwv.
    (* From R w u and R w v derive R u v using symmetry on Hwu then transitivity, then apply Hbp at u *)
    pose proof (R_symm _ _ Hwu) as Huw.
    pose proof (R_trans _ _ _ Huw Hwv) as Huv.
    apply Hbp. exact Huv.
Qed.

Lemma K_sound : forall p q w, box (fun x => p x -> q x) w -> (box p w -> box q w).
Proof.
  intros p q w Himp Hbp u Hwu.
  apply (Himp u Hwu).
  apply (Hbp u Hwu).
Qed.

End S5_Semantics.
