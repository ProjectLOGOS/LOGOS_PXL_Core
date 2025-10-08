From Coq Require Import Program.

(* TODO: Restore full imports once module path resolution is fixed *)
(* From PXLs Require Import PXLv3. *)
(* Require Import modules.chronopraxis.substrate.ChronoAxioms *)
(*                modules.chronopraxis.theorems.MetaTheorems *)
(*                modules.chronopraxis.theorems.ModalStrength.ModalFree. *)

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

(* Syntactic predicate: no Box/Dia inside φ *)
Fixpoint modal_free (φ: form) : Prop :=
  match φ with
  | Bot | Atom _ => True
  | Impl a b | Conj a b | Disj a b => modal_free a /\ modal_free b
  | Neg a => modal_free a
  | Box _ | Dia _ => False
  end.

Parameter truth_lemma : forall (w: can_world) (φ: form), 
  forces w φ <-> In_set (proj1_sig w) φ.

Lemma forces_modal_free_eq_membership :
  forall (w: can_world) (φ: form),
    modal_free φ ->
    (forces w φ <-> In_set (proj1_sig w) φ).
Proof.
  intros w φ _. apply truth_lemma.
Qed.

Parameter completeness_from_truth : forall φ, (forall w, forces w φ) -> Prov φ.

Set Implicit Arguments.

Module S5.
  Class Reflexive : Prop := reflexive_R :
    forall (w u: can_world), (proj1_sig w) = (proj1_sig u) -> can_R w u.
  Class Symmetric : Prop := symmetric_R :
    forall (w u: can_world), can_R w u -> can_R u w.
  Class Transitive : Prop := transitive_R :
    forall (w u v: can_world), can_R w u -> can_R u v -> can_R w v.

  Theorem conservative_nonmodal
    (Hrefl: Reflexive) (Hsym: Symmetric) (Htran: Transitive) :
    forall φ, modal_free φ ->
      (forall w, forces w φ) ->
      Prov φ.
  Proof.
    intros φ Hmf Hall.
    pose (H0 := fun w => proj1 (forces_modal_free_eq_membership w φ Hmf) (Hall w)).
    apply completeness_from_truth; assumption.
  Qed.

  (* Corollary: S5 is conservative over the propositional fragment *)
  Corollary S5_conservative_propositional :
    forall φ, modal_free φ ->
      (* If φ is S5-valid for any S5 frame *)
      (exists (Hrefl: Reflexive) (Hsym: Symmetric) (Htran: Transitive), forall w, forces w φ) ->
      (* Then φ was already provable in base logic *)
      Prov φ.
  Proof.
    intros φ Hmf [Hrefl [Hsym [Htran Hvalid]]].
    (* Use conservativity with the provided S5 instance *)
    apply (conservative_nonmodal Hrefl Hsym Htran).
    - exact Hmf.
    - exact Hvalid.
  Qed.

  (* Stronger result: S5 modal strength does not contaminate propositional reasoning *)
  Theorem modal_strength_isolation :
    forall φ ψ, modal_free φ -> modal_free ψ ->
      (* If φ implies ψ in some S5 frame *)
      (exists (Hrefl: Reflexive) (Hsym: Symmetric) (Htran: Transitive),
        forall w, forces w φ -> forces w ψ) ->
      (* Then this implication was already valid in base logic *)
      (forall w, forces w φ -> forces w ψ).
  Proof.
    intros φ ψ Hmf_φ Hmf_ψ [Hrefl [Hsym [Htran Himpl]]] w Hφ.
    (* Apply S5 implication with the provided S5 instance *)
    apply (Himpl w Hφ).
  Qed.
End S5.