From Coq Require Import List.
Import ListNotations. Set Implicit Arguments.

Inductive form : Type :=
| Atom  : nat -> form
| Bot   : form
| Neg   : form -> form
| Conj  : form -> form -> form
| Disj  : form -> form -> form
| Impl  : form -> form -> form
| Box   : form -> form
| Dia   : form -> form.

Inductive Prov : form -> Prop :=
| ax_K    : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))
| ax_T    : forall p,   Prov (Impl (Box p) p)
| ax_4    : forall p,   Prov (Impl (Box p) (Box (Box p)))
| ax_5    : forall p,   Prov (Impl (Dia p) (Box (Dia p)))
| ax_PL_imp : forall p q r, Prov (Impl (Impl p q) (Impl (Impl q r) (Impl p r)))
| ax_PL_and1 : forall p q, Prov (Impl (Conj p q) p)
| ax_PL_and2 : forall p q, Prov (Impl (Conj p q) q)
| ax_PL_orE  : forall p q r, Prov (Impl (Impl p r) (Impl (Impl q r) (Impl (Disj p q) r)))
| ax_PL_orI1 : forall p q, Prov (Impl p (Disj p q))
| ax_PL_orI2 : forall p q, Prov (Impl q (Disj p q))
| ax_PL_neg_elim : forall p, Prov (Impl (Neg p) (Impl p Bot))
| ax_PL_botE : forall p, Prov (Impl Bot p)
| ax_PL_k : forall p q, Prov (Impl p (Impl q p))
| ax_PL_and_intro : forall p q, Prov (Impl p (Impl q (Conj p q)))
| ax_PL_neg_intro : forall p, Prov (Impl (Impl p Bot) (Neg p))
| ax_PL_imp_exch : forall p q r, Prov (Impl (Impl p (Impl q r)) (Impl q (Impl p r)))
| ax_PL_neg_imp_any : forall a b, Prov (Impl (Neg a) (Impl a b))
| ax_modal_dual_dia_box1 : forall φ, Prov (Impl (Neg (Dia φ)) (Box (Neg φ)))
| ax_modal_dual_dia_box2 : forall φ, Prov (Impl (Box (Neg φ)) (Neg (Dia φ)))
| ax_modal_dual_box_dia1 : forall φ, Prov (Impl (Neg (Box φ)) (Dia (Neg φ)))
| ax_modal_dual_box_dia2 : forall φ, Prov (Impl (Dia (Neg φ)) (Neg (Box φ)))
| mp      : forall p q, Prov (Impl p q) -> Prov p -> Prov q
| nec     : forall p, Prov p -> Prov (Box p).

Lemma mp2 p q r : Prov (Impl p (Impl q r)) -> Prov p -> Prov q -> Prov r.
Proof. intros H1 H2 H3. eapply mp; [eapply mp; eauto|eauto]. Qed.
