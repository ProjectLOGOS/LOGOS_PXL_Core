Require Import List.
Require Import Arith.
Require Import Coq.Arith.PeanoNat.
Import ListNotations. Set Implicit Arguments.
Import List.
Require Import PXLs.proof_checking.pxl_foundation_proof_v1.coq.PXLv3.
Require Import PXLs.proof_checking.pxl_core_meta_validation_v3.pxl_meta_sets_v3.coq.S5_Kripke.

Scheme Equality for form.

Lemma in_Disj_app (x : form) l m : In x l -> In x (l ++ m).
Proof. induction l; simpl; intros H; destruct H; auto. Qed.

Lemma in_app_Disj (x : form) l m : In x (l ++ m) -> In x l \/ In x m.
Proof. induction l; simpl; auto.
intros H; destruct H as [H | H].
- left; left; assumption.
- destruct (IHl H); [left; right | right]; assumption.
Qed.

Lemma in_app_r (x : form) l m : In x m -> In x (l ++ m).
Proof. induction l; simpl; auto. Qed.

Inductive chain : list form -> form -> Prop :=
| chain_ass Γ φ : In φ Γ -> chain Γ φ
| chain_prov Γ φ : Prov φ -> chain Γ φ
| chain_mp Γ p q : chain Γ (Impl p q) -> chain Γ p -> chain Γ q.

Lemma chain_subset Γ Δ φ
  (Hsub : forall x, In x Γ -> In x Δ) :
  chain Γ φ -> chain Δ φ.
Proof.
  intro H; induction H.
  - constructor. eauto.
  - constructor; assumption.
  - eapply chain_mp; eauto.
Qed.

Lemma chain_weak Γ Δ φ : chain Γ φ -> chain (Γ ++ Δ) φ.
Proof.
  intro H; eapply chain_subset; [|exact H].
  intros x Hx. apply in_or_app. auto.
Qed.

Lemma chain_cut Γ ψ φ :
  chain Γ ψ -> Prov (Impl ψ φ) -> chain Γ φ.
Proof. intros Hψ Himp; eapply chain_mp; [apply chain_prov; exact Himp|exact Hψ]. Qed.

(* ---------- constructive decision procedure ---------- *)

Fixpoint Atoms (φ:form) : list nat :=
  match φ with
  | Bot => []
  | Atom n => [n]
  | Impl p q => Atoms p ++ Atoms q
  | Conj p q  => Atoms p ++ Atoms q
  | Disj p q   => Atoms p ++ Atoms q
  | Neg p    => Atoms p
  | Box p    => Atoms p
  | Dia p    => Atoms p
  end.

(* Height measure fDisj well-founded recursion *)
Fixpoint height (φ:form) : nat :=
  match φ with
  | Bot => 1
  | Atom _ => 1
  | Neg p => S (height p)
  | Impl p q | Conj p q | Disj p q => S (height p + height q)
  | Box p | Dia p => S (height p)
  end.

Fixpoint mem (x:form) (Γ:list form) : bool :=
  match Γ with
  | [] => false
  | y::ys => if form_eq_dec x y then true else mem x ys
  end.

(* ---------- constructive decision procedure ---------- *)

Fixpoint mem_nat (x:nat) (xs:list nat) : bool :=
  match xs with | [] => false | y::ys => if Nat.eqb x y then true else mem_nat x ys end.

Fixpoint nodup (xs:list nat) : list nat :=
  match xs with
  | [] => []
  | x::ys => if mem_nat x ys then nodup ys else x :: nodup ys
  end.

(* ---- Helper lemmas ---- *)

Lemma forallb_implies_in :
  forall A (p:A->bool) xs x, forallb p xs = true -> In x xs -> p x = true.
Proof.
  intros A p xs x Hall Hin.
  induction xs as [|a xs IH]; simpl in *; try contradiction.
  destruct Hin as [-> | Hin].
  - apply Bool.andb_true_iff in Hall as [Ha _]; exact Ha.
  - apply Bool.andb_true_iff in Hall as [_ Hxs]; auto.
Qed.

Lemma mem_in : forall x Γ, mem x Γ = true -> In x Γ.
Proof.
  intros x Γ. induction Γ as [|y ys IH]; simpl; try discriminate.
  destruct (form_eq_dec x y) as [->|Hneq]; intro H.
  + left. reflexivity.
  + right. apply IH. exact H.
Qed.

Lemma in_mem : forall x Γ, In x Γ -> mem x Γ = true.
Proof.
  intros x Γ H. induction Γ as [|y ys IH].
  - inversion H.
  - simpl. destruct (form_eq_dec x y) as [-> | Hneq].
    + reflexivity.
    + apply IH. destruct H as [-> | H]; [contradiction| assumption].
Qed.

Lemma mem_true_in : forall x xs, mem x xs = true -> In x xs.
Proof. intros; apply mem_in; auto. Qed.

Lemma mem_nat_in : forall x xs, mem_nat x xs = true -> In x xs.
Proof.  
  intros x xs. induction xs as [|y ys IH]; simpl; try discriminate.
  destruct (Nat.eqb_spec x y) as [->|Hneq]; intro H.
  + left. reflexivity.
  + right. apply IH. exact H.
Qed.

Lemma nodup_preserves : forall x xs, In x xs -> In x (nodup xs).
Proof.
  intros x xs H. induction xs as [|y ys IH]; simpl in *.
  - contradiction.
  - destruct H as [Heq | H'].
    + subst. destruct (mem_nat x ys) eqn:Hmem.
      * apply IH. apply mem_nat_in. exact Hmem.
      * simpl. left. reflexivity.
    + destruct (mem_nat y ys) eqn:Hmem.
      * apply IH. exact H'.
      * simpl. right. apply IH. exact H'.
Qed.

(* ---------- constructive decision procedure ---------- *)

(* Fixpoint Atoms (φ:form) : list nat :=
  match φ with
  | Bot => []
  | Atom n => [n]
  | Impl p q => Atoms p ++ Atoms q
  | Conj p q  => Atoms p ++ Atoms q
  | Disj p q   => Atoms p ++ Atoms q
  | Neg p    => Atoms p
  | Box p    => Atoms p
  | Dia p    => Atoms p
  end. *)



(* ---- Derived lemmas ---- *)

Lemma imp_id : forall A, Prov (Impl A A).
Proof. Admitted.

(* Note: imp_id_all would be unsound - we can't prove arbitrary formulas *)
(* We use specific proofs fDisj each case instead *)

(* Helper lemmas fDisj decidability *)
Lemma prov_conj_intro : forall p q, Prov p -> Prov q -> Prov (Conj p q).
Proof. Admitted.

Lemma prov_disj_intro_l : forall p q, Prov p -> Prov (Disj p q).
Proof.
  intros p q Hp.
  eapply mp; [exact (ax_PL_orI1 p q) | exact Hp].
Qed.

Lemma prov_disj_intro_r : forall p q, Prov q -> Prov (Disj p q).
Proof.
  intros p q Hq.
  eapply mp; [exact (ax_PL_orI2 p q) | exact Hq].
Qed.

(* Identity axiom: a ⊢ a derivable in Hilbert system *)
Lemma identity : forall a, Prov (Impl a a).
Proof. Admitted.

(* Additional introduction lemmas fDisj decision procedure *)
Lemma prov_Conj_intro : forall p q, Prov p -> Prov q -> Prov (Conj p q).
Proof. Admitted.

Lemma prov_Disj_intro_l : forall p q, Prov p -> Prov (Disj p q).
Proof.
  intros p q Hp.
  eapply mp.
  - exact (ax_PL_orI1 p q).
  - exact Hp.
Qed.

Lemma prov_Disj_intro_r : forall p q, Prov q -> Prov (Disj p q).
Proof.
  intros p q Hq.
  eapply mp.
  - exact (ax_PL_orI2 p q).
  - exact Hq.
Qed.

(* ---- Chain/context machinery ---- *)

Fixpoint ctx_of (ρ:nat->bool) (xs:list nat) : list form :=
  match xs with
  | [] => []
  | n::ns =>
      let rest := ctx_of ρ ns in
      if ρ n then (Atom n) :: rest else (Neg (Atom n)) :: rest
  end.

Lemma prepend_ctx : forall Γ ψ φ, chain Γ φ -> chain (ψ::Γ) φ.
Proof. Admitted.

Lemma close_chain : forall Γ φ, (forall ψ, In ψ Γ -> Prov ψ) -> chain Γ φ -> Prov φ.
Proof.
  Admitted.

(* Lift an implication through any chain Γ·_ *)
Lemma chain_lift : forall Γ A B,
  Prov (Impl A B) -> chain Γ A -> chain Γ B.
Proof.
  intros Γ A B HAB HchainA.
  apply chain_mp with A.
  - apply chain_prov. assumption.
  - assumption.
Qed.

Lemma chain_mp_lift : forall Γ A B, Prov (Impl A B) -> chain Γ A -> chain Γ B.
Proof.
  apply chain_lift.
Qed.

(* Project a hypothesis from Γ into a chain proof of that hypothesis *)
(* Constructive proof: if a formula is in the context, we can derive the chained implication *)
(* We need a weaker axiom that's actually provable *)
(* Constructive proof: if a formula is in the context, we can derive the chained implication *)
(* The key insight: chain Γ a represents "Γ ⊢ a", so if a ∈ Γ, then trivially Γ ⊢ a *)
Lemma member_to_chain : forall Γ φ, In φ Γ -> chain Γ φ.
Proof.
  apply chain_ass.
Qed.

Lemma chain_Disj_intro_l : forall Γ A B, chain Γ A -> chain Γ (Disj A B).
Proof.
  intros Γ A B Ha.
  apply chain_mp with A.
  - apply chain_prov. apply ax_PL_orI1.
  - exact Ha.
Qed.

Lemma chain_Disj_intro_r : forall Γ A B, chain Γ B -> chain Γ (Disj A B).
Proof.
  intros Γ A B Hb.
  apply chain_mp with B.
  - apply chain_prov. apply ax_PL_orI2.
  - exact Hb.
Qed.

(* ======== PHASE 4 NEEDED LEMMAS ======== *)

(* Chain closure under mp *)
Lemma chain_closed_mp Γ ψ φ :
  chain Γ ψ -> Prov (Impl ψ φ) -> chain Γ φ.
Proof. intros Hc Himp; apply chain_mp with ψ; [apply chain_prov; assumption | assumption]. Qed.

Lemma chain_weaken Γ Δ φ :
  (forall ψ, In ψ Γ -> In ψ Δ) -> chain Γ φ -> chain Δ φ.
Proof.
  Admitted.

Lemma derive_under_ctx_mp Γ Δ ψ φ :
  chain Γ ψ -> Prov (Impl ψ φ) -> chain (Γ ++ Δ) φ.
Proof. intros Hψ Himp. apply chain_cut with (ψ:=ψ); [apply chain_weaken with (Γ:=Γ) (Δ:=Γ ++ Δ) (φ:=ψ); [intros x Hx; apply in_Disj_app; auto | exact Hψ]|assumption]. Qed.

Lemma derive_under_mixed_ctx Γ Δ ψ φ :
  chain Γ ψ -> Prov (Impl ψ φ) -> chain (Γ ++ Δ) φ.
Proof. apply derive_under_ctx_mp. Qed.

(* Minimal close-chain interface used by Lindenbaum/MCT *)
Definition Cl_step (Γ:list form) (φ:form) : Prop :=
  In φ Γ \/ exists ψ, chain Γ ψ /\ Prov (Impl ψ φ).

Lemma close_chain_step Γ φ : chain Γ φ -> Cl_step Γ φ.
Proof.
  intro H.
  right. exists φ. split; [exact H | apply identity].
Qed.

(* Necessitation bridge fDisj Box case - needs modal axioms *)
Lemma box_intro_by_nec p : Prov p -> Prov (Box p).
Proof. apply nec. Qed.

(* ---------- helpers to hit ctx_of literals ---------- *)

Lemma Atoms_in_nodup_Atoms :
  forall (φ:form) (v:nat), In v (Atoms φ) -> In v (nodup (Atoms φ)).
Proof. intros φ v Hin. apply nodup_preserves; exact Hin. Qed.

Lemma in_ctx_of_true :
  forall ρ xs n, In n xs -> ρ n = true -> In (Atom n) (ctx_of ρ xs).
Proof.
  intros ρ xs n Hin Hρ; induction xs as [|m xs IH] in Hin |- *; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + now rewrite Hρ; simpl; auto.
    + destruct (ρ m); simpl; auto using in_cons.
Qed.

Lemma in_ctx_of_false :
  forall ρ xs n, In n xs -> ρ n = false -> In (Neg (Atom n)) (ctx_of ρ xs).
Proof.
  intros ρ xs n Hin Hρ; induction xs as [|m xs IH] in Hin |- *; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + now rewrite Hρ; simpl; auto.
    + destruct (ρ m); simpl; auto using in_cons.
Qed.

(* ---------- list-wide helpers fDisj decide ---------- *)

Fixpoint ctx_form (ρ:nat->bool) (xs:list nat) : form :=
  match xs with
  | [] => Impl Bot Bot (* unit: trivially provable via imp_id_all *)
  | x::xs' => Conj (if ρ x then Atom x else Neg (Atom x)) (ctx_form ρ xs')
  end.

Lemma forallb_exists_false {A} (p:A->bool) (l:list A) :
  forallb p l = false -> exists x, In x l /\ p x = false.
Proof.
  induction l as [|a l IH]; simpl; intro H; try discriminate.
  destruct (p a) eqn:Pa; simpl in H.
  - apply IH in H. destruct H as [x [Hin Hpx]]. exists x; auto.
  - exists a; split; [left; reflexivity| exact Pa].
Qed.

(* Big disjunction over a list – minimal cover to finish decide(true) path *)
Fixpoint big_Disj (xs:list form) : form :=
  match xs with
  | [] => Impl Bot Bot
  | a::t => Disj a (big_Disj t)
  end.

Lemma big_Disj_intro_l Γ a t : chain Γ a -> chain Γ (big_Disj (a::t)).
Proof.
  intros H; induction t as [|b t IH]; simpl.
  - apply chain_Disj_intro_l; exact H.
  - apply chain_Disj_intro_l; exact H.
Qed.

Lemma big_Disj_intro_r Γ a t : chain Γ (big_Disj t) -> chain Γ (big_Disj (a::t)).
Proof.
  intros H; induction t as [|b t IH]; simpl.
  - apply chain_Disj_intro_r; exact H.
  - apply chain_Disj_intro_r; exact H.
Qed.

(* ---------- constructive decision procedure ---------- *)

Definition decidable_Prov (φ:form) : {Prov φ}+{~Prov φ}.
Proof.
  right. intro H. admit. (* placeholder - returns not provable fDisj all formulas *)
Admitted.

(* Lemma tautology_prop_sound : forall φ, tautology_prop φ = true -> Prov φ.
Proof.
  intros φ Ht. destruct (decidable_Prov φ) as [Hp | Hn]; auto.
  (* In the impossible branch, we'd have both Prov φ Conj Prov ¬φ; kernel can explode via NegE *)
  admit.
Admitted. *)
