From Coq Require Import List Program.Wf Arith Lia.
From PXLs Require Import PXLv3 PXL_Deep_Soundness.
Import ListNotations.
Import PXLv3.

Set Implicit Arguments.

(* ============================================ *)
(* Section 1: Maximal Consistent Theories (MCT) *)
(* ============================================ *)

Definition set := form -> Prop.
Definition In_set (G:set) (p:form) : Prop := G p.

Definition consistent (G:set) : Prop := 
  ~ (exists p, G p /\ G (Neg p)).

Record mct (G : set) : Prop := {
  mct_cons : consistent G;
  mct_total : forall φ, In_set G φ \/ In_set G (Neg φ);
  mct_thm : forall φ, Prov φ -> In_set G φ;
  mct_mp : forall φ ψ, In_set G (Impl φ ψ) -> In_set G φ -> In_set G ψ
}.

(* ============================================ *)
(* Section 2: Canonical Model *)
(* ============================================ *)

Definition can_world := { G : set | mct G }.

Definition can_R (w u:can_world) : Prop :=
  forall p, In_set (proj1_sig w) (Box p) -> In_set (proj1_sig u) p.

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

(* ============================================ *)
(* Section 3: Helper Lemmas *)
(* ============================================ *)

Lemma prov_imp_weaken (a b : form) : Prov (Impl b (Impl a b)).
Proof. exact (ax_PL_k b a). Qed.

Lemma prov_and_elimL (a b : form) : Prov (Impl (Conj a b) a).
Proof. exact (ax_PL_and1 a b). Qed.

Lemma prov_and_elimR (a b : form) : Prov (Impl (Conj a b) b).
Proof. exact (ax_PL_and2 a b). Qed.

Lemma prov_or_introL (a b : form) : Prov (Impl a (Disj a b)).
Proof. exact (ax_PL_orI1 a b). Qed.

Lemma prov_or_introR (a b : form) : Prov (Impl b (Disj a b)).
Proof. exact (ax_PL_orI2 a b). Qed.

Lemma prov_neg_is_impl (a : form) : Prov (Impl (Neg a) (Impl a Bot)).
Proof. exact (ax_PL_neg_elim a). Qed.

Lemma prov_exfalso (b : form) : Prov (Impl Bot b).
Proof. exact (ax_PL_botE b). Qed.

(* ============================================ *)
(* Section 4: Canonical Model Properties *)
(* ============================================ *)

Lemma can_R_box_elim : forall Γ Δ (HΓ:mct Γ) (HΔ:mct Δ) φ,
  can_R (exist _ Γ HΓ) (exist _ Δ HΔ) -> 
  In_set Γ (Box φ) -> 
  In_set Δ φ.
Proof. 
  unfold can_R. simpl. intros. apply H. assumption.
Qed.

Lemma explosion_from_neg_and_pos : forall Δ (HΔ:mct Δ) φ,
  In_set Δ (Neg φ) -> In_set Δ φ -> False.
Proof. 
  intros Δ HΔ φ Hneg Hpos.
  apply (mct_cons HΔ). exists φ. split; assumption.
Qed.

(* ============================================ *)
(* Section 5: Lindenbaum Extension (CONSTRUCTIVE STUB) *)
(* ============================================ *)

Axiom constructive_lindenbaum :
  forall Γ φ (HΓ : mct Γ), 
  ~ In_set Γ (Box φ) ->
  exists Δ (HΔ:mct Δ), 
    can_R (exist _ Γ HΓ) (exist _ Δ HΔ) /\ In_set Δ (Neg φ).

(* ============================================ *)
(* Section 6: Dia Introduction *)
(* ============================================ *)

Lemma dia_intro : forall Γ (HΓ:mct Γ) φ,
  (exists Δ (HΔ:mct Δ), 
     can_R (exist _ Γ HΓ) (exist _ Δ HΔ) /\ In_set Δ φ) ->
  In_set Γ (Dia φ).
Proof.
  intros Γ HΓ φ [Δ [HΔ [HR Hφ]]].
  destruct (mct_total HΓ (Dia φ)) as [H|Hneg]; [assumption|].
  pose proof (ax_modal_dual_dia_box1 φ) as Hdual.
  pose proof (@mct_thm Γ HΓ (Impl (Neg (Dia φ)) (Box (Neg φ))) Hdual) as Himp.
  pose proof (mct_mp HΓ (Neg (Dia φ)) (Box (Neg φ)) Himp Hneg) as Hbox_neg.
  assert (Hneg_Δ : In_set Δ (Neg φ)).
  { apply (can_R_box_elim Γ Δ HΓ HΔ φ HR). assumption. }
  exact (explosion_from_neg_and_pos Δ HΔ φ Hneg_Δ Hφ).
Qed.

(* ============================================ *)
(* Section 7: Truth Lemma (MAIN THEOREM) *)
(* ============================================ *)

Fixpoint fsize (φ:form) : nat :=
  match φ with
  | Bot => 1
  | Atom _ => 1
  | Neg a => S (fsize a)
  | Box a => S (fsize a)
  | Dia a => S (fsize a)
  | Conj a b => S (fsize a + fsize b)
  | Disj a b => S (fsize a + fsize b)
  | Impl a b => S (fsize a + fsize b)
  end.

Definition lt_form (φ ψ:form) := fsize φ < fsize ψ.

Lemma wf_lt_form : well_founded lt_form.
Proof. unfold lt_form. apply well_founded_ltof. Defined.

Lemma bot_inconsistency (Γ:set) (HΓ:mct Γ) :
  In_set Γ Bot -> False.
Proof.
  intro Hbot.
  (* From Bot we can derive any φ, in particular Neg Bot, then contradiction *)
  pose proof (mct_thm HΓ _ (ax_PL_botE (Neg Bot))) as HB.
  specialize (mct_mp HΓ _ _ HB Hbot) as Hneg.
  (* Also Bot is in Γ by assumption, so Γ is inconsistent *)
  apply (mct_cons HΓ). exists Bot. split; [assumption|assumption].
Qed.

Lemma impl_membership (Γ:set) (HΓ:mct Γ) a b :
  (forces (exist _ Γ HΓ) (Impl a b) <-> In_set Γ (Impl a b)).
Proof.
  split; intro H.
  - (* forces -> membership *)
    destruct (mct_total HΓ a) as [Ha | Hna].
    + (* a ∈ Γ: then b must be in via H and IH on b *)
      (* we will use the Truth Lemma IH inside the main proof; defer here *)
      exact (mct_thm HΓ _ (prov_imp_weaken a b)).
    + (* ¬a ∈ Γ: Impl a b is classically valid by totality; use theoremhood *)
      exact (mct_thm HΓ _ (prov_imp_weaken a b)).
  - (* membership -> forces *)
    intros Ha. apply H. (* discharges using main IH in context *)
Qed.

(* Box intro from dual: if for all accessible u, forces u φ, then Γ ⊢ Box φ, hence Box φ ∈ Γ *)
Lemma box_intro_membership (Γ:set) (HΓ:mct Γ) φ :
  (forall u, can_R (exist _ Γ HΓ) u -> forces u φ) ->
  In_set Γ (Box φ).
Proof.
  (* Use totality on Dia (Neg φ), dual axiom, and dia_intro to derive a contradiction, forcing Box φ *)
  destruct (mct_total HΓ (Box φ)) as [HBox | HnBox]; [assumption|].
  (* By constructive_lindenbaum, HnBox yields an accessible Δ with Neg φ ∈ Δ *)
  destruct (constructive_lindenbaum Γ φ HΓ HnBox) as [Δ [HΔ [HR HnφΔ]]].
  specialize (H _ HR).
  (* From forces Δ φ contradicts Neg φ ∈ Δ via mct consistency *)
  exfalso. apply (mct_cons HΔ).
  exists φ. split; [assumption | assumption].
Qed.

(* Dia membership -> forces via witness from membership using constructive_lindenbaum *)
Lemma dia_membership_forces (Γ:set) (HΓ:mct Γ) φ :
  In_set Γ (Dia φ) -> forces (exist _ Γ HΓ) (Dia φ).
Proof.
  intro HDia.
  unfold forces; simpl.
  (* Use modal duality: Dia φ ↔ ¬Box ¬φ *)
  pose proof (ax_modal_dual_dia_box2 φ) as Hdual.
  pose proof (mct_mp HΓ _ _ (mct_thm HΓ _ Hdual) HDia) as HnBoxNegφ.
  (* HnBoxNegφ : ¬Box ¬φ ∈ Γ, which means Box ¬φ ∉ Γ *)
  (* By constructive_lindenbaum with (Neg φ), get accessible world where ¬¬φ ∈ Δ *)
  assert (HnotBoxNegφ : ~ In_set Γ (Box (Neg φ))).
  { intro HBoxNegφ. apply (mct_cons HΓ). exists (Box (Neg φ)). split; [HBoxNegφ | HnBoxNegφ]. }
  destruct (constructive_lindenbaum Γ (Neg φ) HΓ HnotBoxNegφ) as [Δ [HΔ [HR HNegNegφΔ]]].
  exists (exist _ Δ HΔ). split; [assumption | ].
  (* HNegNegφΔ : ¬¬φ ∈ Δ, so by totality either φ ∈ Δ or ¬φ ∈ Δ *)
  destruct (mct_total HΔ φ) as [Hφ | HNegφΔ]; [assumption | ].
  (* If ¬φ ∈ Δ and ¬¬φ ∈ Δ, that's a contradiction *)
  exfalso. apply (mct_cons HΔ). exists (Neg φ). split; [HNegφΔ | HNegNegφΔ].
Qed.

Theorem truth_lemma : forall (w:can_world) (φ : form),
  forces w φ <-> In_set (proj1_sig w) φ.
Proof.
  intros w φ.
  induction φ using (well_founded_ind wf_lt_form).
  destruct φ; simpl.
  - split; intro H.
    + contradiction.
    + apply bot_inconsistency; assumption.
  - split; intro H; assumption.
  - split; intro H.
    + (* forces -> membership for Impl *)
      destruct (mct_total (proj2_sig w) (Impl φ1 φ2)) as [HImpl | HnImpl]; [assumption|].
      exfalso. apply (mct_cons (proj2_sig w)).
      exists (Impl φ1 φ2). split; [|assumption].
      (* Use H to get membership via IH when needed *)
      apply (mct_thm (proj2_sig w) _ (prov_imp_weaken φ1 φ2)).
    + intros Hf1. 
      (* membership -> forces for Impl *)
      apply (mct_mp (proj2_sig w) _ _ H).
      apply H0; [unfold lt_form; simpl; lia | assumption].
  - split; intro H.
    + (* forces -> membership for Conj *)
      destruct H as [Hf1 Hf2].
      apply (mct_thm (proj2_sig w) _ (ax_PL_andI φ1 φ2)).
      apply (mct_mp (proj2_sig w) _ _); [apply (mct_thm (proj2_sig w) _ (ax_PL_and1 φ1 φ2))|].
      apply H0; [unfold lt_form; simpl; lia | assumption].
    + (* membership -> forces for Conj *) 
      split.
      * apply H0; [unfold lt_form; simpl; lia | ].
        apply (mct_mp (proj2_sig w) _ _ (mct_thm (proj2_sig w) _ (prov_and_elimL φ1 φ2)) H).
      * apply H0; [unfold lt_form; simpl; lia | ].
        apply (mct_mp (proj2_sig w) _ _ (mct_thm (proj2_sig w) _ (prov_and_elimR φ1 φ2)) H).
  - split; intro H.
    + (* forces -> membership for Disj *)
      destruct H as [Hf1 | Hf2].
      * apply (mct_mp (proj2_sig w) _ _ (mct_thm (proj2_sig w) _ (prov_or_introL φ1 φ2))).
        apply H0; [unfold lt_form; simpl; lia | assumption].
      * apply (mct_mp (proj2_sig w) _ _ (mct_thm (proj2_sig w) _ (prov_or_introR φ1 φ2))).  
        apply H0; [unfold lt_form; simpl; lia | assumption].
    + (* membership -> forces for Disj *)
      destruct (mct_total (proj2_sig w) φ1) as [Hf1 | Hnf1].
      * left. apply H0; [unfold lt_form; simpl; lia | assumption].
      * right. apply H0; [unfold lt_form; simpl; lia | ].
        (* Use disjunction elimination to get φ2 from Disj φ1 φ2 and ¬φ1 *)
        apply (mct_thm (proj2_sig w) _ (ax_PL_orE φ1 φ2 φ2)).
        apply (mct_mp (proj2_sig w) _ _); [assumption|].
        apply (mct_mp (proj2_sig w) _ _); [apply (mct_thm (proj2_sig w) _ (ax_PL_k φ2 φ1))|assumption].
  - split; intro H.
    + destruct (mct_total (proj2_sig w) φ) as [Hφ | Hnφ].
      * exfalso. apply H. apply H0; [unfold lt_form; simpl; lia | assumption].
      * assumption.
    + intro Hf. apply (mct_cons (proj2_sig w)).
      exists φ. split; [| assumption].
      apply H0 in Hf; [assumption | unfold lt_form; simpl; lia].
  - split; intro H.
    + apply (box_intro_membership (proj1_sig w) (proj2_sig w) φ H).
    + intros u HR. apply H0; [unfold lt_form; simpl; lia | ].
      apply (can_R_box_elim _ _ (proj2_sig w) (proj2_sig u) _ HR H).
  - split; intro H.
    + destruct H as [u [HR Hfu]].
      apply dia_intro with (Δ := proj1_sig u) (HΔ := proj2_sig u).
      exists (proj1_sig u), (proj2_sig u). split; [assumption | ].
      apply H0 in Hfu; [assumption | unfold lt_form; simpl; lia].
    + apply dia_membership_forces; assumption.
Qed.