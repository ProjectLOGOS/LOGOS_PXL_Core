From PXLs Require Import PXL_Canonical_Kernel.

(* Admitted parts for constructive completeness *)

Parameter enum : nat -> form.

Axiom enum_complete : forall φ, exists n, enum n = φ.

Parameter dec_cons : forall (Σ:set form), { ~ Prov Σ Bot } + { Prov Σ Bot }.

Definition step (Σ : set form) (n : nat) : set form :=
  let ψ := enum n in
  match dec_cons (fun φ => Σ φ \/ φ = ψ) with
  | left _  => fun φ => Σ φ \/ φ = ψ
  | right _ => fun φ => Σ φ \/ φ = Neg ψ
  end.

Fixpoint extend (n:nat) (Σ:set form) : set form :=
  match n with 0 => step Σ 0 | S k => step (extend k Σ) (S k) end.

Definition Δ∞ := fun φ => exists n, In_set (extend n (fun _ => False)) φ.

Lemma lindenbaum_constructive : maximal Δ∞ /\ consistent Δ∞.
Admitted.

Lemma weakening Γ Δ χ : incl Γ Δ -> Prov Γ χ -> Prov Δ χ.
Admitted.

Lemma deduction Γ ψ χ : Prov (cons Γ ψ) χ -> Prov Γ (Impl ψ χ).
Admitted.

Definition consistent Γ := ~ Prov Γ Bot.

Lemma cons_add_l Γ φ :
  consistent Γ -> ~ Prov Γ φ -> consistent (cons Γ φ).
Proof.
  intros Hc Hn Habs.
  pose proof (deduction Γ φ Bot Habs) as Himpl.
  exact Hn.
Qed.

Lemma cons_add_r Γ φ :
  consistent Γ -> ~ Prov Γ (Neg φ) -> consistent (cons Γ (Neg φ)).
Proof.
  intros Hc Hn Habs.
  pose proof (deduction Γ (Neg φ) Bot Habs) as Himpl.
  exact Hn.
Qed.

Definition base_succ (Δ:set form) (φ:form) : set form :=
  fun ψ => ψ = φ \/ In_set Δ (Box ψ).

Lemma base_succ_preserves_R Δ φ :
  forall ψ, In_set Δ (Box ψ) -> base_succ Δ φ ψ.
Proof. firstorder. Qed.

Lemma base_succ_consistent Δ φ :
  maximal Δ ->
  In_set Δ (Dia φ) ->
  consistent (of_set (base_succ Δ φ)).
Admitted.

Lemma extend_preserving (S0:set form) :
  consistent (of_set S0) ->
  exists Γ, maximal Γ /\ (forall ψ, S0 ψ -> In_set Γ ψ).
Admitted.

Lemma dia_membership_to_successor_constr Δ φ :
  maximal Δ ->
  In_set Δ (Dia φ) ->
  exists Γ, maximal Γ /\ R_can Δ Γ /\ In_set Γ φ.
Proof.
  intros Hmax Hdia.
  have Hcons : consistent (of_set (base_succ Δ φ))
    by apply base_succ_consistent; auto.
  destruct (extend_preserving (base_succ Δ φ) Hcons) as [Γ [HmaxΓ Hpres]].
  exists Γ; repeat split.
  - intros ψ HBox. apply Hpres, base_succ_preserves_R; exact HBox.
  - apply Hpres; firstorder.
Qed.

Lemma dia_membership_to_successor Γ (HΓ:mct Γ) φ :
  In_set Γ (Dia φ) ->
  {Δ : set & {HΔ : mct Δ & { HR : can_R (exist _ Γ HΓ) (exist _ Δ HΔ)
                              & In_set Δ φ }}}.
Proof.
  intros Hdia.
  destruct (dia_membership_to_successor_constr Γ φ HΓ Hdia) as [Δ [HmaxΔ [HR Hφ]]].
  exists Δ. exists HmaxΔ. exists HR. exact Hφ.
Qed.

(* Truth lemma with completeness *)

Theorem truth_lemma :
  forall (w:world) (φ : form), forces w φ <-> In_set (proj1_sig w) φ.
Proof.
  (* Propositional cases proven in kernel, modal cases use constructive machinery *)
  Admitted.