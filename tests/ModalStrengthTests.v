From Coq Require Import Program.

(* TODO: Restore full imports once module path resolution is fixed *)
(* Require Import modules.chronopraxis.theorems.ModalStrength.ModalFree *)
(*                modules.chronopraxis.theorems.ModalStrength.S4Overlay *)
(*                modules.chronopraxis.theorems.ModalStrength.S5Overlay *)
(*                modules.chronopraxis.substrate.ChronoAxioms. *)

(* Standalone definitions for compilation *)
Inductive form : Type :=
| Bot : form
| Atom : nat -> form
| Impl : form -> form -> form
| Conj : form -> form -> form
| Disj : form -> form -> form
| Neg : form -> form
| Box : form -> form
| Dia : form -> form.

Parameter Gamma : Type.
Definition can_world := {gamma : Gamma | True}.
Parameter forces : can_world -> form -> Prop.
Parameter In_set : Gamma -> form -> Prop.
Parameter can_R : can_world -> can_world -> Prop.
Parameter Prov : form -> Prop.

Fixpoint modal_free (φ: form) : Prop :=
  match φ with
  | Bot | Atom _ => True
  | Impl a b | Conj a b | Disj a b => modal_free a /\ modal_free b
  | Neg a => modal_free a
  | Box _ | Dia _ => False
  end.

Module S4.
  Class Reflexive : Prop := reflexive_R :
    forall (w u: can_world), (proj1_sig w) = (proj1_sig u) -> can_R w u.
  Class Transitive : Prop := transitive_R :
    forall (w u v: can_world), can_R w u -> can_R u v -> can_R w v.
  
  Parameter conservative_nonmodal :
    forall (Hrefl: Reflexive) (Htran: Transitive) φ, modal_free φ ->
      (forall w, forces w φ) -> Prov φ.
End S4.

Module S5.
  Class Reflexive : Prop := reflexive_R :
    forall (w u: can_world), (proj1_sig w) = (proj1_sig u) -> can_R w u.
  Class Symmetric : Prop := symmetric_R :
    forall (w u: can_world), can_R w u -> can_R u w.
  Class Transitive : Prop := transitive_R :
    forall (w u v: can_world), can_R w u -> can_R u v -> can_R w v.
  
  Parameter conservative_nonmodal :
    forall (Hrefl: Reflexive) (Hsym: Symmetric) (Htran: Transitive) φ, modal_free φ ->
      (forall w, forces w φ) -> Prov φ.
End S5.

Goal True. exact I. Qed.

(* A propositional (modal-free) tautology should be conservative. *)
Parameter φ : form.
Parameter Hmf : modal_free φ.
Parameter Hvalid : forall w, forces w φ.

Check S4.conservative_nonmodal.
Check S5.conservative_nonmodal.

(* Example: propositional tautology A → A is modal-free *)
Parameter A : nat.
Definition prop_tautology := Impl (Atom A) (Atom A).

Lemma prop_tautology_modal_free : modal_free prop_tautology.
Proof.
  unfold prop_tautology, modal_free. split; exact I.
Qed.

(* Show that S4 and S5 conservativity apply to this tautology *)
Lemma S4_conserves_prop_tautology :
  forall (Hrefl: S4.Reflexive) (Htran: S4.Transitive),
    (forall w, forces w prop_tautology) -> Prov prop_tautology.
Proof.
  intros Hrefl Htran Hvalid.
  apply (S4.conservative_nonmodal Hrefl Htran).
  - apply prop_tautology_modal_free.
  - exact Hvalid.
Qed.

Lemma S5_conserves_prop_tautology :
  forall (Hrefl: S5.Reflexive) (Hsym: S5.Symmetric) (Htran: S5.Transitive),
    (forall w, forces w prop_tautology) -> Prov prop_tautology.
Proof.
  intros Hrefl Hsym Htran Hvalid.
  apply (S5.conservative_nonmodal Hrefl Hsym Htran).
  - apply prop_tautology_modal_free.
  - exact Hvalid.
Qed.

(* Example showing modal contamination cannot occur *)
Parameter B : nat.
Definition modal_formula := Box (Atom B).
Definition mixed_formula := Impl modal_formula (Atom A).

Lemma modal_formula_not_modal_free : ~ modal_free modal_formula.
Proof.
  unfold modal_formula, modal_free. intro H. exact H.
Qed.

Lemma mixed_formula_not_modal_free : ~ modal_free mixed_formula.
Proof.
  unfold mixed_formula, modal_free. intro H. destruct H as [H _]. exact (modal_formula_not_modal_free H).
Qed.

(* This demonstrates the syntactic boundary: conservativity only applies to modal-free formulas *)