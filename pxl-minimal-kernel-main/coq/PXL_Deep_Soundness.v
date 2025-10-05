From Coq Require Import Logic.Classical.

(*
  PXL_Deep_Soundness.v
  Deep embedding of a propositional modal language with S5 rules.
  Proves: If Prov φ then φ is valid on any frame with equivalence R.
  Explicit proofs only.
*)

Section Deep.

(* Syntax *)
Inductive form : Type :=
| Bot  : form
| Var  : nat -> form
| Impl : form -> form -> form
| And  : form -> form -> form
| Or   : form -> form -> form
| Neg  : form -> form
| Box  : form -> form
| Dia  : form -> form.

(* Frames and semantics *)
Record frame := {
  W : Type;
  R : W -> W -> Prop;
  R_refl  : forall w, R w w;
  R_symm  : forall w u, R w u -> R u w;
  R_trans : forall w u v, R w u -> R u v -> R w v
}.

Definition valuation (F:frame) := nat -> (W F) -> Prop.

Fixpoint eval (F:frame) (v:valuation F) (w:W F) (φ:form) {struct φ} : Prop :=
  match φ with
  | Bot      => False
  | Var n    => v n w
  | Impl p q => eval F v w p -> eval F v w q
  | And p q  => eval F v w p /\ eval F v w q
  | Or p q   => eval F v w p \/ eval F v w q
  | Neg p    => ~ eval F v w p
  | Box p    => forall u, R F w u -> eval F v u p
  | Dia p    => exists u, R F w u /\ eval F v u p
  end.

Definition valid_on (F:frame) (φ:form) : Prop :=
  forall (v:valuation F) (w:W F), eval F v w φ.

(* Proof system *)
Inductive Prov : form -> Prop :=
| ax_K  : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))
| ax_T  : forall p,   Prov (Impl (Box p) p)
| ax_4  : forall p,   Prov (Impl (Box p) (Box (Box p)))
| ax_5  : forall p,   Prov (Impl (Dia p) (Box (Dia p)))
| ax_PL_imp : forall p q r,
    Prov (Impl (Impl p q) (Impl (Impl q r) (Impl p r)))
| ax_PL_and1 : forall p q, Prov (Impl (And p q) p)
| ax_PL_and2 : forall p q, Prov (Impl (And p q) q)
| mp    : forall p q, Prov (Impl p q) -> Prov p -> Prov q
| nec   : forall p, Prov p -> Prov (Box p).

(* Soundness of axioms and rules *)
Lemma sound_K : forall (F:frame) (v:valuation F) (w:W F) (p q:form),
  eval F v w (Impl (Box (Impl p q)) (Impl (Box p) (Box q))).
Proof.
  intros F v w p q Hb Hp u Hwu.
  exact ((Hb u Hwu) (Hp u Hwu)).
Qed.

Lemma sound_T : forall (F:frame) (v:valuation F) (w:W F) (p:form),
  eval F v w (Impl (Box p) p).
Proof.
  intros F v w p Hb. apply Hb. apply (R_refl F).
Qed.

Lemma sound_4 : forall (F:frame) (v:valuation F) (w:W F) (p:form),
  eval F v w (Impl (Box p) (Box (Box p))).
Proof.
  intros F v w p Hb u Hwu t Hut. apply Hb. eapply (R_trans F); eauto.
Qed.

Lemma sound_5 : forall (F:frame) (v:valuation F) (w:W F) (p:form),
  eval F v w (Impl (Dia p) (Box (Dia p))).
Proof.
  intros F v w p [u [Hwu Hpu]] t Hwt. exists u. split.
  - eapply (R_trans F). apply (R_symm F). exact Hwt. exact Hwu.
  - exact Hpu.
Qed.

Lemma sound_PL_imp : forall (F:frame) (v:valuation F) (w:W F) (p q r:form),
  eval F v w (Impl (Impl p q) (Impl (Impl q r) (Impl p r))).
Proof.
  intros F v w p q r Hpqr Hqr Hp. apply Hqr. apply Hpqr. exact Hp.
Qed.

Lemma sound_PL_and1 : forall (F:frame) (v:valuation F) (w:W F) (p q:form),
  eval F v w (Impl (And p q) p).
Proof.
  intros F v w p q [Hp _]. exact Hp.
Qed.

Lemma sound_PL_and2 : forall (F:frame) (v:valuation F) (w:W F) (p q:form),
  eval F v w (Impl (And p q) q).
Proof.
  intros F v w p q [_ Hq]. exact Hq.
Qed.

Lemma sound_mp : forall (F:frame) (p q:form),
  valid_on F (Impl p q) -> valid_on F p -> valid_on F q.
Proof.
  intros F p q Hpq Hp v w. exact ((Hpq v w) (Hp v w)).
Qed.

Lemma sound_nec : forall (F:frame) (p:form),
  valid_on F p -> valid_on F (Box p).
Proof.
  intros F p H v w u Hwu. apply (H v u).
Qed.

Fixpoint soundness (F:frame) (φ:form) (H:Prov φ) : valid_on F φ :=
  match H in Prov φ return valid_on F φ with
  | ax_K p q => fun v w => sound_K F v w p q
  | ax_T p => fun v w => sound_T F v w p
  | ax_4 p => fun v w => sound_4 F v w p
  | ax_5 p => fun v w => sound_5 F v w p
  | ax_PL_imp p q r => fun v w => sound_PL_imp F v w p q r
  | ax_PL_and1 p q => fun v w => sound_PL_and1 F v w p q
  | ax_PL_and2 p q => fun v w => sound_PL_and2 F v w p q
  | mp p q H1 H2 => fun v w => sound_mp F p q (soundness F (Impl p q) H1) (soundness F p H2) v w
  | nec p H1 => fun v w => sound_nec F p (soundness F p H1) v w
  end.

End Deep.
