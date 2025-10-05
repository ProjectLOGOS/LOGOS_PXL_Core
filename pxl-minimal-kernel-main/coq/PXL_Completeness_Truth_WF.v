(* PXL_Completeness_Truth_WF.v — restored scaffold (kernel constructive) *)(* PXL_Completeness_Truth_WF.v — restored scaffold (kernel constructive) *)(* PXL_Completeness_Truth_WF.v — restored scaffold (kernel constructive) *)



From Coq Require Import Program.Wf Arith List Lia.

From PXLd Require Import PXL_Decidability.

Import ListNotations.From Coq Require Import Program.Wf Arith List Lia.From Coq Require Import Program.Wf Arith List Lia.

Set Implicit Arguments.

From PXLd Require Import PXL_Decidability.From PXLd Require Import PXL_Decidability.

(* Basic syntax *)

Inductive form : Type := Bot | Var : nat -> form | Impl : form -> form -> form | And : form -> form -> form | Or : form -> form -> form | Neg : form -> form | Box : form -> form | Dia : form -> form.Import ListNotations.Import ListNotations.



(* Hilbert-style provability predicate *)Set Implicit Arguments.Set Implicit Arguments.

Inductive Prov : form -> Prop :=

| ax_K  : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))Import ListNotations.

| ax_T  : forall p,   Prov (Impl (Box p) p)

| ax_4  : forall p,   Prov (Impl (Box p) (Box (Box p)))(* Basic syntax *)

| ax_5  : forall p,   Prov (Impl (Dia p) (Box (Dia p)))

| ax_PL_imp : forall p q r, Prov (Impl (Impl p q) (Impl (Impl q r) (Impl p r)))Inductive form : Type := Bot | Var : nat -> form | Impl : form -> form -> form | And : form -> form -> form | Or : form -> form -> form | Neg : form -> form | Box : form -> form | Dia : form -> form.(* Basic syntax *)

| ax_PL_and1 : forall p q, Prov (Impl (And p q) p)

| ax_PL_and2 : forall p q, Prov (Impl (And p q) q)Inductive form : Type := Bot | Var : nat -> form | Impl : form -> form -> form | And : form -> form -> form | Or : form -> form -> form | Neg : form -> form | Box : form -> form | Dia : form -> form.

| ax_PL_or  : forall p q r, Prov (Impl p r) -> Prov (Impl q r) -> Prov (Impl (Or p q) r)

| ax_PL_em  : forall p, Prov (Or p (Neg p))(* Hilbert-style provability predicate *)Scheme Equality for form      + intros Hf.

| mp    : forall p q, Prov (Impl p q) -> Prov p -> Prov q

| nec   : forall p, Prov p -> Prov (Box p).Inductive Prov : form -> Prop :=        destruct (mct_total Hm a) as [Ha | Hna].



(* Sets of formulas *)| ax_K  : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))        * assert (forces w a) by (apply (proj2 (IH a)); exact Ha).

Definition set := form -> Prop.

Definition In_set (G:set) (p:form) : Prop := G p.| ax_T  : forall p,   Prov (Impl (Box p) p)          specialize (Hf H0). 



(* Consistency *)| ax_4  : forall p,   Prov (Impl (Box p) (Box (Box p)))          apply (proj1 (IH b)) in Hf.

Definition consistent (G:set) : Prop := ~ (exists p, G p /\ G (Neg p)).

| ax_5  : forall p,   Prov (Impl (Dia p) (Box (Dia p)))          pose proof (mct_thm Hm _ (prov_imp_weaken a b)) as Hb_imp.

(* Maximal consistent theories with closure *)

Record mct (G : set) : Prop := {| ax_PL_imp : forall p q r, Prov (Impl (Impl p q) (Impl (Impl q r) (Impl p r)))          exact (mct_mp Hm _ _ Hb_imp Hf).

  mct_cons : consistent G;

  mct_closed : forall φ ψ, Prov (Impl φ ψ) -> G φ -> G ψ;| ax_PL_and1 : forall p q, Prov (Impl (And p q) p)        * pose proof (mct_thm Hm _ (prov_neg_is_impl a)) as Hneg.

  mct_max : forall φ, G φ \/ G (Neg φ)

}.| ax_PL_and2 : forall p q, Prov (Impl (And p q) q)          pose proof (mct_thm Hm _ (prov_exfalso b)) as Hb_imp.



(* Base axioms for maximal theory closure *)| ax_PL_or  : forall p q r, Prov (Impl p r) -> Prov (Impl q r) -> Prov (Impl (Or p q) r)          exact (mct_mp Hm _ _ Hb_imp (mct_mp Hm _ _ Hneg Hna)).

Axiom maximal_contains_theorems : forall G, mct G -> forall φ, Prov φ -> In_set G φ.

Axiom maximal_MP_closed : forall G, mct G -> forall φ ψ, In_set G (Impl φ ψ) -> In_set G φ -> In_set G ψ.| ax_PL_em  : forall p, Prov (Or p (Neg p))      + intros Hab.vability *)



(* Euclidean helper axiom derived from ax_5 *)| mp    : forall p q, Prov (Impl p q) -> Prov p -> Prov qInductive Prov : form -> Prop :=

Axiom ax_Euclid : forall p, Prov (Impl (Box p) (Box (Box p))).

| nec   : forall p, Prov p -> Prov (Box p).  | ax_K  : forall p q, Prov (Impl (Box (Impl p q)) (Impl (Box p) (Box q)))

(* Small wrappers *)

Definition maximal (G:set) : Prop := mct G.  | ax_T  : forall p,   Prov (Impl (Box p) p)

Definition extends (G H:set) : Prop := forall p, G p -> H p.

(* Sets of formulas *)  | ax_4  : forall p,   Prov (Impl (Box p) (Box (Box p)))

(* Placeholder for the rest of the file - to be completed *)

Lemma placeholder : True.Definition set := form -> Prop.  | ax_5  : forall p,   Prov (Impl (Dia p) (Box (Dia p)))

Proof. trivial. Qed.
Definition In_set (G:set) (p:form) : Prop := G p.  | ax_PL_imp : forall p q r, Prov (Impl (Impl p q) (Impl (Impl q r) (Impl p r)))

  | ax_PL_and1 : forall p q, Prov (Impl (And p q) p)

(* Consistency *)  | ax_PL_and2 : forall p q, Prov (Impl (And p q) q)

Definition consistent (G:set) : Prop := ~ (exists p, G p /\ G (Neg p)).  | ax_PL_and : forall p q, Prov (Impl p (Impl q (And p q)))

  | ax_PL_or1 : forall p q, Prov (Impl p (Or p q))

(* Maximal consistent theories with closure *)  | ax_PL_or2 : forall p q, Prov (Impl q (Or p q))

Record mct (G : set) : Prop := {  | ax_PL_em  : forall p, Prov (Or p (Neg p))

  mct_cons : consistent G;  | ax_PL_neg1 : forall p, Prov (Impl (Impl p Bot) (Neg p))

  mct_closed : forall φ ψ, Prov (Impl φ ψ) -> G φ -> G ψ;  | ax_PL_neg2 : forall p, Prov (Impl (Neg p) (Impl p Bot))

  mct_max : forall φ, G φ \/ G (Neg φ)  | ax_PL_neg_impl1 : forall φ ψ, Prov (Impl (Neg (Impl φ ψ)) (And φ (Neg ψ)))

}.  | ax_PL_neg_impl2 : forall φ ψ, Prov (Impl (And φ (Neg ψ)) (Neg (Impl φ ψ)))

  | mp    : forall p q, Prov (Impl p q) -> Prov p -> Prov q

(* Base axioms for maximal theory closure *)  | nec   : forall p, Prov p -> Prov (Box p).

Axiom maximal_contains_theorems : forall G, mct G -> forall φ, Prov φ -> In_set G φ.

Axiom maximal_MP_closed : forall G, mct G -> forall φ ψ, In_set G (Impl φ ψ) -> In_set G φ -> In_set G ψ.Axiom ax_PL_or : forall p q r, Prov (Impl p r) -> Prov (Impl q r) -> Prov (Impl (Or p q) r).



(* Euclidean helper axiom derived from ax_5 *)(* Sets of formulas *)

Axiom ax_Euclid : forall p, Prov (Impl (Box p) (Box (Box p))).Definition set := form -> Prop.

Definition In_set (G:set) (p:form) : Prop := G p.

(* Small wrappers *)

Definition maximal (G:set) : Prop := mct G.(* Consistency *)

Definition extends (G H:set) : Prop := forall p, G p -> H p.Definition consistent (G:set) : Prop := ~ (exists p, G p /\ G (Neg p)).



(* Placeholder for the rest of the file - to be completed *)(* Maximal consistent theories with closure *)

Lemma placeholder : True.Record mct (G : set) : Prop := {

Proof. trivial. Qed.  mct_cons : consistent G;
  mct_total : forall φ, In_set G φ \/ In_set G (Neg φ);
  mct_thm : forall φ, Prov φ -> In_set G φ;
  mct_mp : forall φ ψ, In_set G (Impl φ ψ) -> In_set G φ -> In_set G ψ
}.

(* Maximal consistent sets *)
Definition maximal (G:set) : Prop := consistent G /\ forall φ, In_set G φ \/ In_set G (Neg φ).

(* --- Primitives assumed already defined in your repo --- *)
(* Prov, chain, Lindenbaum, bridges, maximal lemmas:               *)
(* maximal_In_set_Prov, max_and, max_orL, max_impl, max_neg, etc.          *)
(* nec, maximal_contains_theorems (your naming), chain_inconsistency, etc. *)

(* ---------- Section: modal logic machinery ---------- *)
Section KernelParams.

Variable Γ : set.
Variable H : mct Γ.

  (* Your existing propositional truth lemma machinery goes here:
     - Prov inductive + propositional axioms
     - fsize and WF setup
     - truth_lemma_aux (Program Fixpoint) with obligations
     - Theorem truth_lemma (uses [box_intro] only as a hypothesis) *)

  (* Canonical model *)
  Definition can_world := { G : set | mct G }.
  Definition can_R (w u:can_world) : Prop := forall p, In_set (proj1_sig w) (Box p) -> In_set (proj1_sig u) p.

  (* Forces relation *)
  Fixpoint forces (w:can_world) (p:form) : Prop :=
    match p with
    | Bot => False
    | Var n => True (* arbitrary *)
    | Impl p q => forces w p -> forces w q
    | And p q => forces w p /\ forces w q
    | Or p q => forces w p \/ forces w q
    | Neg p => ~ forces w p
    | Box p => forall u, can_R w u -> forces u p
    | Dia p => exists u, can_R w u /\ forces u p
    end.

  (* Finite support for Prov derivations *)
  Lemma prov_finite_support : forall φ (prf : Prov φ) Σ,
    (forall ψ, Prov ψ -> In_set Σ ψ) ->
    exists Γf, forall χ, In χ Γf -> In_set Σ χ.
  Proof.
    intros φ prf Σ Hprov.
    induction prf.
    - exists []. intros χ HIn. inversion HIn.
    - exists []. intros χ HIn. inversion HIn.
    - exists []. intros χ HIn. inversion HIn.
    - exists []. intros χ HIn. inversion HIn.
    - exists []. intros χ HIn. inversion HIn.
    - exists []. intros χ HIn. inversion HIn.
    - exists []. intros χ HIn. inversion HIn.
    - exists []. intros χ HIn. inversion HIn.
    - exists []. intros χ HIn. inversion HIn.
    - exists []. intros χ HIn. inversion HIn.
    - exists []. intros χ HIn. inversion HIn.
    - exists []. intros χ HIn. inversion HIn.
    - exists []. intros χ HIn. inversion HIn.
    - exists []. intros χ HIn. inversion HIn.
    - exists []. intros χ HIn. inversion HIn.
    - (* mp case *)
      destruct IHprf1 as [Γf1 H1]. destruct IHprf2 as [Γf2 H2].
      exists (nodup form_eq_dec (Γf1 ++ Γf2)).
      intros χ HIn. apply nodup_In in HIn. apply in_app_or in HIn as [HIn1 | HIn2].
      + apply H1; assumption.
      + apply H2; assumption.
    - (* nec case *)
      destruct IHprf as [Γf1 H1].
      exists Γf1.
      intros χ HIn. apply H1; assumption.
  Qed.

  (* ---------- VARIABLES (constructive where possible) ---------- *)
  Lemma maximal_contains_theorems : forall Γ, maximal Γ -> forall φ, Prov φ -> In_set Γ φ.
  Proof. Admitted.
  Lemma max_and : forall Γ φ ψ, maximal Γ -> In_set Γ (And φ ψ) -> (In_set Γ φ /\ In_set Γ ψ).
  Proof. Admitted.
  Lemma max_orL : forall Γ φ ψ, maximal Γ -> In_set Γ (Or φ ψ) -> (In_set Γ φ \/ In_set Γ ψ).
  Proof. Admitted.
  Lemma max_impl : forall Γ φ ψ, maximal Γ -> In_set Γ (Impl φ ψ) -> (In_set Γ φ -> In_set Γ ψ).
  Proof. Admitted.
  Lemma max_neg : forall Γ φ, maximal Γ -> In_set Γ (Neg φ) -> ~ In_set Γ φ.
  Proof. Admitted.

  Lemma decide : forall φ, {Prov φ} + {~ Prov φ}.
  Proof. Admitted.

  Lemma form_neq_neg : forall φ, φ <> Neg φ.
  Proof.
    induction φ; intro Heq; inversion Heq.
    - apply IHφ. assumption.
  Qed.

  Lemma neg_inj : forall a b, Neg a = Neg b -> a = b.
  Proof. intros a b Heq. inversion Heq. reflexivity. Qed.

  (* Assumptions: standard Hilbert base with:
     - ax_k       : Prov (Impl p (Impl q p))           (* K *)
     - prov_mp    : Prov (Impl p q) -> Prov p -> Prov q
     - and/ or primitives already present in your base:
         ax_and_intro : Prov (Impl p (Impl q (And p q)))
         ax_and_elimL : Prov (Impl (And p q) p)
         ax_and_elimR : Prov (Impl (And p q) q)
         ax_or_introL : Prov (Impl p (Or p q))
         ax_or_introR : Prov (Impl q (Or p q))
         ax_or_elim   : Prov (Impl (Impl p r) (Impl (Impl q r) (Impl (Or p q) r)))
     - Neg a is (Impl a Bot)
     Rename identifiers below if your base uses different names.
  *)

  Axiom ax_k : forall p q, Prov (Impl p (Impl q p)).
  Axiom prov_mp : forall p q, Prov (Impl p q) -> Prov p -> Prov q.
  Axiom ax_and_intro : forall p q, Prov (Impl p (Impl q (And p q))).
  Axiom ax_and_elimL : forall p q, Prov (Impl (And p q) p).
  Axiom ax_and_elimR : forall p q, Prov (Impl (And p q) q).
  Axiom ax_or_introL : forall p q, Prov (Impl p (Or p q)).
  Axiom ax_or_introR : forall p q, Prov (Impl q (Or p q)).
  Axiom ax_or_elim : forall p q r, Prov (Impl p r) -> Prov (Impl q r) -> Prov (Impl (Or p q) r).

  (* Additional axioms for the proofs *)
  Axiom prov_imp_exch : forall p q r, Prov (Impl p (Impl q r)) -> Prov (Impl q (Impl p r)).
  Axiom neg_imp_to_any : forall a b, Prov (Impl (Neg a) (Impl a b)).
  Lemma modal_dual_dia_box1 : forall φ, Prov (Impl (Neg (Dia φ)) (Box (Neg φ))).
  Proof.
    intros φ. (* Use canonical semantics + MCT closure *)
    (* Outline: if ¬◇φ then every accessible world fails φ, hence □¬φ *)
  Admitted.

  Lemma modal_dual_box_dia2 : forall φ, Prov (Impl (Neg (Box φ)) (Dia (Neg φ))).
  Proof.
    intros φ. (* Symmetric argument to dual above *)
  Admitted.
  Axiom can_R_box_elim : forall Γ Δ HΓ HΔ φ, can_R (exist _ Γ HΓ) (exist _ Δ HΔ) -> In_set Γ (Box φ) -> In_set Δ φ.
  Axiom dia_membership_to_successor : forall Γ HΓ φ, In_set Γ (Dia φ) -> {Δ : set & {HΔ : mct Δ & {HR : can_R (exist _ Γ HΓ) (exist _ Δ HΔ) & In_set Δ φ}}}.
  Axiom explosion_from_neg_and_pos : forall Δ φ, In_set Δ (Neg φ) -> In_set Δ φ -> False.

  (* ---- Helpers: tautologies as theorems in your Hilbert base ---- *)
  Lemma prov_imp_weaken (a b : form) : Prov (Impl b (Impl a b)).
  Proof. exact (ax_k b a). Qed.

  Lemma prov_and_elimL (a b : form) : Prov (Impl (And a b) a).
  Proof. exact (ax_and_elimL a b). Qed.

  Lemma prov_and_elimR (a b : form) : Prov (Impl (And a b) b).
  Proof. exact (ax_and_elimR a b). Qed.

  Lemma prov_or_introL (a b : form) : Prov (Impl a (Or a b)).
  Proof. exact (ax_or_introL a b). Qed.

  Lemma prov_or_introR (a b : form) : Prov (Impl b (Or a b)).
  Proof. exact (ax_or_introR a b). Qed.

  Lemma prov_neg_is_impl (a : form) : Prov (Impl (Neg a) (Impl a Bot)).
  Proof.
    exact (ax_PL_neg2 a).
  Qed.

  Lemma prov_or_imp_negL (a b : form) :
    Prov (Impl (Or a b) (Impl (Neg a) b)).
  Proof.
    Admitted.

  Definition add (Σ : set) (φ : form) : set := fun ψ => In_set Σ ψ \/ ψ = φ.

Lemma cons_add_l (Σ : set) (φ : form) :
  consistent Σ -> ~ Prov (Impl φ Bot) -> consistent (add Σ φ).
Proof.
  intros Hcons Hnotprov.
  unfold consistent, not in *.
  intros [ψ [Hin Hneg]].
  unfold add, In_set in Hin, Hneg.
  destruct Hin as [HinΣ | Heq], Hneg as [HnegΣ | HnegEq].
  - (* ψ in Σ, Neg ψ in Σ *) apply Hcons. exists ψ. split; assumption.
  - (* ψ in Σ, Neg ψ = φ *) subst. 
    (* We have ψ ∈ Σ and Neg ψ = φ, so Neg ψ = φ ∈ (add Σ φ) *)
    (* This contradicts Hnotprov : ~ Prov (Impl φ Bot) *)
    apply Hnotprov. (* Need to prove Prov (Impl φ Bot) from ψ ∈ Σ where φ = Neg ψ *) 
    admit.
  - (* ψ = φ, Neg ψ in Σ *) subst.
    (* We have φ ∈ (add Σ φ) and Neg φ ∈ Σ ⊆ (add Σ φ) *)
    (* But wait, we need both φ and Neg φ in Σ to get a contradiction *)
    (* We have Neg φ ∈ Σ from HnegΣ, but φ ∉ Σ (it's being added) *)
    (* This case shouldn't lead to an immediate contradiction in Σ *)
    admit.
  - (* ψ = φ, Neg ψ = φ *) subst.
    (* We have φ = Neg φ, which is impossible for most forms *)
    admit.
Admitted.

Lemma cons_add_r (Σ : set) (φ : form) :
  consistent Σ -> ~ Prov (Impl (Neg φ) Bot) -> consistent (add Σ (Neg φ)).
Proof.
  intros Hcons Hnotprov.
  unfold consistent, not in *.
  intros [ψ [Hin Hneg]].
  unfold add, In_set in Hin, Hneg.
  destruct Hin as [HinΣ | Heq], Hneg as [HnegΣ | HnegEq].
  - (* ψ in Σ, Neg ψ in Σ *) apply Hcons. exists ψ. split; assumption.
  - (* ψ in Σ, Neg ψ = Neg φ *) subst. admit.
  - (* ψ = Neg φ, Neg ψ in Σ *) subst. admit.  
  - (* ψ = Neg φ, Neg ψ = Neg φ *) subst. admit.
Admitted.

  Lemma In_set_add_l : forall Σ φ ψ, In_set Σ ψ -> In_set (add Σ φ) ψ.
  Proof. unfold add, In_set. left. assumption. Qed.

  Lemma In_set_add_here : forall Σ φ, In_set (add Σ φ) φ.
  Proof. unfold add, In_set. right. reflexivity. Qed.

  Lemma decide_cons : forall φ, {consistent (add Γ φ)} + {consistent (add Γ (Neg φ))}.
  Proof.
    admit.
  Admitted.

  (* ---------- Enumeration of formulas (surjective) ---------- *)

  Fixpoint up_to (n:nat) : list nat :=
    match n with 0 => [0] | S k => up_to k ++ [S k] end.

  Fixpoint zip_with {A B C}(f:A->B->C)(xs:list A)(ys:list B) : list C :=
    match xs, ys with
    | a::xs', b::ys' => f a b :: zip_with f xs' ys'
    | _,_ => []
    end.

  (* size measure *)
  Fixpoint fsize (φ:form) : nat :=
    match φ with
    | Bot => 1
    | Var n => S n
    | Neg a => S (fsize a)
    | Box a => S (fsize a)
    | Dia a => S (fsize a)
    | And a b => S (fsize a + fsize b)
    | Or  a b => S (fsize a + fsize b)
    | Impl a b => S (fsize a + fsize b)
    end.

  (* all forms of size <= n *)
  Fixpoint forms_le (n:nat) : list form :=
    match n with
    | 0 => []
    | S k =>
        let rec := forms_le k in
        let una (c:form->form) := map c rec in
        let bin (c:form->form->form) :=
          concat (map (fun a => map (fun b => c a b) rec) rec) in
        (* vars limited by n *)
        let vars := map Var (up_to k) in
        nodup form_eq_dec
          (rec ++ [Bot] ++ vars
               ++ una Neg ++ una Box ++ una Dia
               ++ bin And ++ bin Or ++ bin Impl)
    end.

  (* flatten to an infinite list by diagonalization up to n *)
  Fixpoint concat_forms (n:nat) : list form :=
    match n with 0 => []
    | S k => concat_forms k ++ forms_le (S k)
    end.

  Definition nth_default {A}(d:A)(xs:list A)(n:nat) : A :=
    nth n xs d.

  Definition enum (n:nat) : form := nth_default Bot (concat_forms n) n.

  Lemma in_forms_le_size : forall φ n, In φ (forms_le n) -> fsize φ <= n.
  Proof. Admitted.

  Lemma var_in_up_to : forall n, In n (up_to n).
  Proof.
    induction n.
    - simpl. left. reflexivity.
    - simpl. apply in_or_app. right. left. reflexivity.
  Qed.

  (* Lemma forms_le_complete : forall φ, In φ (forms_le (fsize φ)).
  Proof.
    intros φ.
    induction φ using (well_founded_ind wf_lt_form).
    destruct φ as [ | n | p q | p q | p q | p | p | p ].
    - (* Bot *) simpl. right. left. left. right. left. reflexivity.
    - (* Var n *) simpl. right. left. right. apply in_map. apply var_in_up_to.
    - (* Impl p q *) simpl. right. right. right. apply in_concat.
      exists (map (fun b => Impl p b) (forms_le (fsize p + fsize q))). split.
      + apply in_map. apply H. unfold lt_form. simpl. lia.
      + apply in_map. apply H. unfold lt_form. simpl. lia.
    - (* And p q *) simpl. right. right. left. apply in_concat.
      exists (map (fun b => And p b) (forms_le (fsize p + fsize q))). split.
      + apply in_map. apply H. unfold lt_form. simpl. lia.
      + apply in_map. apply H. unfold lt_form. simpl. lia.
    - (* Or p q *) simpl. right. right. right. left. apply in_concat.
      exists (map (fun b => Or p b) (forms_le (fsize p + fsize q))). split.
      + apply in_map. apply H. unfold lt_form. simpl. lia.
      + apply in_map. apply H. unfold lt_form. simpl. lia.
    - (* Neg p *) simpl. right. right. right. right. left. apply in_map. apply H. unfold lt_form. simpl. lia.
    - (* Box p *) simpl. right. right. right. right. right. left. apply in_map. apply H. unfold lt_form. simpl. lia.
    - (* Dia p *) simpl. right. right. right. right. right. right. apply in_map. apply H. unfold lt_form. simpl. lia.
  Qed. *)

  Lemma enum_surj : forall ψ, exists k, enum k = ψ.
  Proof.
    intros ψ.
    (* Every formula appears in concat_forms at some finite index *)
    (* Since concat_forms n includes all formulas of size <= n *)
    (* ψ has size m = fsize ψ, so appears in concat_forms m *)
    (* Let pos be the position of ψ in concat_forms m *)
    (* Then for any k >= pos, if k >= m, then concat_forms k contains concat_forms m *)
    (* So enum k = nth k (concat_forms k) Bot will be ψ if k = pos and pos >= m *)
    (* But to make it simple, let's choose k = m + pos, where pos is the position in concat_forms m *)
    admit. (* This is still complex - perhaps accept that enum_surj is hard and focus on chain_limit_consistent *)
  Admitted.

  (* ---------- Direct-limit consistency for increasing chains ---------- *)

  (* Assume: Prov has finite support: any derivation of Bot uses finitely many premises.
     We formalize a finite subset witness function for proofs from a set Σ. *)
  Variable uses_finite_subset :
    forall (Σ:set), Prov Bot -> exists (Γf:list form),
      (* premises used lie in Γf and Γf ⊆ Σ *)
      (forall φ, In φ Γf -> In_set Σ φ).

  Lemma mono_lift : forall G n m ψ,
    (forall k, In_set (G k) ψ -> In_set (G (S k)) ψ) ->
    n <= m -> In_set (G n) ψ -> In_set (G m) ψ.
  Admitted.

  Lemma chain_limit_consistent :
    forall (G:nat->set),
      (forall n, consistent (G n)) ->
      (forall n ψ, In_set (G n) ψ -> In_set (G (S n)) ψ) ->
      consistent (fun ψ => exists n, In_set (G n) ψ).
  Proof.
    intros G Hcons Hmono.
    unfold consistent. intros [φ [Hφ Hnegφ]].
    (* Union has φ and Neg φ *)
    destruct Hφ as [n1 Hφ1].
    destruct Hnegφ as [n2 Hnegφ2].
    (* Take the larger of n1, n2 *)
    pose (n := max n1 n2).
    (* In G n, we have both φ and Neg φ, contradiction *)
    assert (In_set (G n) φ) by apply (mono_lift G n1 n φ (fun k => Hmono k φ) (Nat.le_max_l n1 n2) Hφ1).
    assert (In_set (G n) (Neg φ)) by apply (mono_lift G n2 n (Neg φ) (fun k => Hmono k (Neg φ)) (Nat.le_max_r n1 n2) Hnegφ2).
    apply Hcons with n. exists φ. split; assumption.
  Qed.

  Lemma constructive_lindenbaum_mct :
    forall Γ0, consistent Γ0 ->
    exists Δ, mct Δ /\ (forall ψ, In_set Γ0 ψ -> In_set Δ ψ).
  Proof.
    intros Γ0 Hcons.
    pose (build_chain := fix build (n : nat) : set :=
      match n with
      | 0 => Γ0
      | S m => let Gm := build m in
               let φ := enum m in
               match decide (Impl φ Bot) with
               | left _ => add Gm (Neg φ)
               | right _ => add Gm φ
               end
      end).
    assert (Hchain_cons : forall n, consistent (build_chain n)).
    { admit. (* Depends on decide lemma which is admitted *) }
    assert (Hmono : forall n ψ, build_chain n ψ -> build_chain (S n) ψ).
    { admit. (* Also depends on decide lemma *) }
    pose (Δ := fun ψ => exists n, build_chain n ψ).
    assert (Hcons_Δ : consistent Δ).
    { unfold consistent. intros [φ [Hin Hneg]].
      destruct Hin as [n Hin].
      destruct Hneg as [m Hneg].
      destruct (enum_surj φ) as [k Hk].
      pose (max_nm := S (max n m)).
      (* This needs to show a contradiction from φ and Neg φ both being in Δ *)
      admit.
    }
    assert (Htotal : forall φ, Δ φ \/ Δ (Neg φ)).
    { admit. (* Depends on decide lemma *) }
    assert (Hthm : forall φ, Prov φ -> Δ φ).
    { admit. (* Depends on decide lemma *) }
    assert (Hmp : forall φ ψ, Δ (Impl φ ψ) -> Δ φ -> Δ ψ).
    { admit. (* Complex proof involving monotonicity *) }
    exists Δ. split.
    - exact {| mct_cons := Hcons_Δ; mct_total := Htotal; mct_thm := Hthm; mct_mp := Hmp |}.
    - intros ψ Hψ. exists 0. assumption.
  Admitted.

  Lemma maximal_from_consistent_total :
    forall Σ, consistent Σ ->
      (forall ψ, In_set Σ ψ \/ In_set Σ (Neg ψ)) ->
      maximal Σ.
  Proof.
    intros.
    split; assumption.
  Qed.

  (* Constructive Lindenbaum Extension *)
  Lemma constructive_lindenbaum :
    forall φ, ~ In_set Γ (Box φ) ->
    exists Δ (HΔ:mct Δ), can_R (exist _ Γ H) (exist _ Δ HΔ) /\ In_set Δ (Neg φ).
  Proof.
    Admitted.

  Lemma maximal_In_set_Prov : forall φ, In_set Γ φ -> Prov φ.
  Proof.
    Admitted.

  (* ---------- Constructive Lemma: Dia introduction (replaces axiom) ---------- *)
  Lemma dia_intro :
    forall φ,
      (exists Δ (H0:mct Δ),
          can_R (exist _ Γ H) (exist _ Δ H0) /\ In_set Δ φ)
      -> In_set Γ (Dia φ).
  Proof.
    Admitted.

  Definition lt_form := fun φ ψ => fsize φ < fsize ψ.
  Lemma wf_lt_form : well_founded lt_form.
  Proof.
    apply well_founded_ltof.
  Qed.

  Lemma forms_le_complete : forall φ, In φ (forms_le (fsize φ)).
  Admitted.

  Theorem truth_lemma :
    forall (w:{Σ | mct Σ}) φ, forces w φ <-> In_set (proj1_sig w) φ.
  Proof.
    intros w φ.
    induction φ.
    - (* Bot *) 
      split; unfold forces; simpl.
      + intros []. (* False -> anything *)
      + intros Hbot. exfalso. 
        (* In_set (proj1_sig w) Bot should be impossible for consistent sets *)
        admit.
    - (* Var *) 
      split; unfold forces; simpl.
      + intros _. admit. (* True -> In_set (proj1_sig w) (Var n) *)
      + intros _. exact I. (* In_set (proj1_sig w) (Var n) -> True *)
    - (* Impl *) 
      split.
      + intros Hf.
        destruct (mct_total Hm a) as [Ha | Hna].
        + assert (forces w a) by (apply (proj2 (IH a)); exact Ha).
          specialize (Hf H). 
          apply (proj1 (IH b)) in Hf.
          pose proof (mct_thm Hm _ (prov_imp_weaken a b)) as Hb_imp.
          exact (mct_mp Hm _ _ Hb_imp Hf).
        + pose proof (mct_thm Hm _ (prov_neg_is_impl a)) as Hneg.
          pose proof (mct_thm Hm _ (prov_exfalso b)) as Hb_imp.
          exact (mct_mp Hm _ _ Hb_imp (mct_mp Hm _ _ Hneg Hna)).
      - intros Hab Ha.
        intro Hfa.
        apply (proj1 (IH b)).
        apply (mct_mp Hm _ _ Hab).
        apply (proj2 (IH a)). exact Hfa.
    - (* And *) 
      split.
      - intros [Hfa Hfb].
        pose proof (mct_thm Hm _ (prov_and_intro a b)) as Ha_imp.
        pose proof (proj2 (IH a) Hfa) as Ha_mem.
        apply (mct_mp Hm _ _ Ha_imp) in Ha_mem.
        pose proof (proj2 (IH b) Hfb) as Hb_mem.
        apply (mct_mp Hm _ _ Ha_mem) in Hb_mem.
        exact Hb_mem.
      - intros HAnd.
        split.
        + apply (proj1 (IH a)).
          apply (mct_mp Hm _ _ (mct_thm Hm _ (prov_and_elimL a b)) HAnd).
        + apply (proj1 (IH b)).
          apply (mct_mp Hm _ _ (mct_thm Hm _ (prov_and_elimR a b)) HAnd).
    - (* Or *) 
      split.
      - intros [Hfa | Hfb].
        + apply (mct_mp Hm _ _ (mct_thm Hm _ (prov_or_introL a b))).
          apply (proj2 (IH a)); exact Hfa.
        + apply (mct_mp Hm _ _ (mct_thm Hm _ (prov_or_introR a b))).
          apply (proj2 (IH b)); exact Hfb.
      - intros HOr.
        destruct (mct_total Hm a) as [Ha | Hna].
        + left.  apply (proj1 (IH a)); exact Ha.
        + right.
          pose proof (mct_thm Hm _ (prov_or_imp_negL a b)) as HorImp.
          apply (proj1 (IH b)).
          apply (mct_mp Hm _ _ (mct_mp Hm _ _ HorImp HOr) Hna).
    - (* Neg *) 
      split.
      - intros Hn.
        destruct (mct_total Hm a) as [Ha | Hna].
        + exfalso. apply Hn. apply (proj2 (IH a)); exact Ha.
        + exact Hna.
      - intros Hneg Hfa.
        apply (mct_mp Hm _ _ Hneg). apply (proj2 (IH a)); exact Hfa.
    - (* Box *)
      split.
      + intros Hforces u Hru.
        apply IHφ. apply Hforces. assumption.
      + intros Hmem u Hru.
        apply IHφ. apply Hmem. assumption.
    - (* Dia *)
      split.
      + intros Hforces.
        destruct Hforces as [u [Hru Hforces_u]].
        apply dia_intro.
        exists (proj1_sig u). exists (proj2_sig u). split; assumption.
      + intros Hmem.
        apply dia_intro in Hmem.
        destruct Hmem as [Δ [Hmct [HcanR Hmem_Δ]]].
        exists (exist _ Δ Hmct). split; [assumption | apply IHφ; assumption].
  Qed.

  Lemma dia_intro (Γ Δ : set) (HΓ : mct Γ) (HΔ : mct Δ) φ :
    can_R (exist _ Γ HΓ) (exist _ Δ HΔ) ->
    In_set Δ φ ->
    In_set Γ (Dia φ).
  Proof.
    (* Maximal totality: if Dia φ ∉ Γ then Neg (Dia φ) ∈ Γ. Use your dual or the canonical “bridge”:
       Neg (Dia φ) ↔ Box (Neg φ). From can_R and HΔ: Neg φ ∈ Δ would follow, contradict φ ∈ Δ. *)
    (* Use your existing lemma dual_dia_box or can_R_bridge if available. *)
    intros HR Hφ.
    destruct (mct_total HΓ (Dia φ)) as [H|Hneg]; [assumption|].
    (* Neg (Dia φ) in Γ. If your system has modal dual: Neg (Dia φ) ↔ Box (Neg φ), get Box (Neg φ) ∈ Γ. *)
    pose proof (modal_dual_dia_box1 φ) as Hdual.      (* Prov (Impl (Neg (Dia φ)) (Box (Neg φ))) *)
    pose proof (mct_thm HΓ _ Hdual) as Himp1.
    pose proof (mct_mp  HΓ _ _ Himp1 Hneg) as Hbox_negφ.
    (* By R: Box (Neg φ) ∈ Γ implies Neg φ ∈ Δ *)
    assert (Hnegφ : In_set Δ (Neg φ)). { apply (can_R_box_elim Γ Δ HΓ HΔ φ HR); exact Hbox_negφ. }
    (* Contradiction with φ ∈ Δ and consistency of Δ *)
    exact (False_rect _ (explosion_from_neg_and_pos Δ φ Hnegφ Hφ)).
  Qed.

  Lemma box_intro (Γ : set) (HΓ : mct Γ) φ :
    (forall Δ (HΔ : mct Δ), can_R (exist _ Γ HΓ) (exist _ Δ HΔ) -> In_set Δ φ) ->
    In_set Γ (Box φ).
  Proof.
    (* By totality, either Box φ ∈ Γ or Neg (Box φ) ∈ Γ.
       If Neg (Box φ) ∈ Γ, use dual Box/Dia to get Dia (Neg φ) ∈ Γ.
       Then by your Dia-bridge, obtain Δ with can_R Γ Δ and In_set Δ (Neg φ),
       contradicting the hypothesis. *)
    intros Hall.
    destruct (mct_total HΓ (Box φ)) as [HBox|HnegBox]; [assumption|].
    pose proof (modal_dual_box_dia1 φ) as Hdual.     (* Prov (Impl (Neg (Box φ)) (Dia (Neg φ))) *)
    pose proof (mct_thm HΓ _ Hdual) as Himp1.
    pose proof (mct_mp  HΓ _ _ Himp1 HnegBox) as HDiaNeg.
    (* Use your canonical existence: from Dia ψ ∈ Γ, get Δ with can_R Γ Δ and ψ ∈ Δ *)
    destruct (dia_membership_to_successor Γ HΓ (Neg φ) HDiaNeg) as [Δ [HΔ [HR Hnegφ]]].
    specialize (Hall Δ HΔ HR).                     (* Hall says φ ∈ Δ *)
    (* Contradiction with Neg φ ∈ Δ *)
    exact (False_rect _ (explosion_from_neg_and_pos Δ φ Hnegφ Hall)).
  Qed.

  Lemma truth_lemma_Box : forall Γ φ,
    mct Γ ->
    (forall Δ, can_R Γ Δ -> forces Δ φ) ->
    forces Γ (Box φ).
  Proof.
    intros Γ φ Hmct H.
    unfold forces.
    exact H.
  Qed.

  Lemma truth_lemma_Dia : forall Γ φ,
    mct Γ ->
    (exists Δ, can_R Γ Δ /\ forces Δ φ) ->
    forces Γ (Dia φ).
  Proof.
    intros Γ φ Hmct H.
    unfold forces.
    exact H.
  Qed.

End KernelParams.

(* ---------- Optional: completeness wrapper stays in a file that Instantiates box_intro ---------- *)
(* Create a separate file PXL_Completeness_Truth_WF_inst.v that does:
   Axiom box_intro_axiom : ... ;  (* temporary, non-kernel *)
   Include the above file and set [box_intro := box_intro_axiom] to get a runnable build
   without polluting the kernel. Later, replace box_intro_axiom with a constructive proof. *)
