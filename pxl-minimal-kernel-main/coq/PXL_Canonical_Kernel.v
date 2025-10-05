From Coq Require Import List.
Import ListNotations.
Require Import PXLv3 PXL_Deep_Soundness Assumptions.

Lemma modal_dual_dia_box1 φ :
  Prov (Impl (Dia φ) (Neg (Box (Neg φ)))).
Proof. exact (ax_dual_dia_box φ). Qed.

Lemma modal_dual_box_dia2 φ :
  Prov (Impl (Neg (Box φ)) (Dia (Neg φ))).
Proof. exact (ax_dual_box_dia φ). Qed.

(* --- Basic sets and MCT structure with Hilbert closure --- *)

Definition set := form -> Prop.

Definition In_set (G:set) (p:form) : Prop := G p.

Definition consistent (G:set) : Prop := ~ (exists p, G p /\ G (Neg p)).

Record mct (G:set) : Prop := {
  mct_cons  : consistent G;
  mct_thm   : forall φ : form, Prov φ -> G φ;                    (* theorems in the set *)
  mct_mp    : forall φ ψ : form, G (Impl φ ψ) -> G φ -> G ψ;     (* closed under MP *)
  mct_total : forall φ : form, G φ \/ G (Neg φ)                  (* maximality *)
}.

(* --- Canonical worlds, accessibility --- *)

Definition world := { G : set | mct G }.

Definition can_R (w u:world) : Prop :=
  forall p, In_set (proj1_sig w) (Box p) -> In_set (proj1_sig u) p.

(* --- Kripke forcing aligned with membership for Var --- *)

Fixpoint forces (w:world) (p:form) : Prop :=
  match p with
  | Bot      => False
  | Var n    => In_set (proj1_sig w) (Var n)
  | Impl a b => (forces w a -> forces w b)
  | And a b  => forces w a /\ forces w b
  | Or  a b  => forces w a \/ forces w b
  | Neg a    => ~ forces w a
  | Box a    => forall u, can_R w u -> forces u a
  | Dia a    => exists u, can_R w u /\ forces u a
  end.

(* --- Propositional helpers (from PXLv3 constructors) --- *)

Lemma prov_imp_weaken (a b : form) : Prov (Impl b (Impl a b)).
Proof. exact (ax_K b a). Qed.

Lemma prov_or_imp_negL (a b : form) : Prov (Impl (Or a b) (Impl (Neg a) b)).
Proof.
  (* Use ax_or_elim with r := Impl (Neg a) b *)
  (* Need: Prov (Impl a (Impl (Neg a) b)) and Prov (Impl b (Impl (Neg a) b)) *)
  pose proof (prov_imp_weaken (Neg a) b) as Hb.
  (* For a -> (a -> b): from neg_imp_to_any we have (a -> a -> b),
     use ax_PL_imp to rotate/compose: (a -> (a -> a)) then chain to b *)
  pose proof (neg_imp_to_any a b) as Hna.    (* (a) -> (a -> b) *)
  (* derive a -> (a -> b) using ax_PL_imp *)
  (* ax_PL_imp p q r : ((p->q)->((q->r)->(p->r))) *)
  pose proof (ax_PL_imp (Neg a) a b) as Hcomp.
  (* First build (a -> (a -> a)) *)
  pose proof (prov_imp_weaken a (Neg a)) as Ha_na_a.    (* a -> (a -> a) *)
  (* Now compose (a -> (a -> a)) with ((a)->(a->b)) to get (a -> (a -> b)) *)
  apply (mp _ _ (ax_or_elim a b (Impl (Neg a) b)));
  [ (* left branch: a -> (a -> b) *)
    eapply mp; [exact (mp _ _ Hcomp Ha_na_a)|]; exact Hna
  | (* right branch: b -> (?a -> b) *)
    exact Hb
  ].
Qed.

(* --- Canonical forcing respects Prov --- *)

Lemma can_R_box_elim Γ Δ (HΓ:mct Γ) (HΔ:mct Δ) φ :
  can_R (exist _ Γ HΓ) (exist _ Δ HΔ) -> In_set Γ (Box φ) -> In_set Δ φ.
Proof. unfold can_R. simpl. firstorder. Qed.

Lemma explosion_from_neg_and_pos Δ (HΔ:mct Δ) φ :
  In_set Δ (Neg φ) -> In_set Δ φ -> False.
Proof. intros H1 H2. apply (mct_cons HΔ). exists φ. split; assumption. Qed.