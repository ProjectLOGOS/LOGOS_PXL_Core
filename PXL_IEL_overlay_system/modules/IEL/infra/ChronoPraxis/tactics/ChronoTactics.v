Require Import PXLs.IEL.Infra.ChronoPraxis.Substrate.Bijection
               PXLs.IEL.Infra.ChronoPraxis.Substrate.ChronoMappings.

(* Specialized rewrite lemmas for bijection normalization *)
Lemma AB_back_fwd : forall x, ChronoMappings.B_to_A (ChronoMappings.A_to_B x) = x.
Proof.
  intro x. 
  (* B_to_A (A_to_B x) = backward (forward x) = x by fg_rewrite *)
  unfold ChronoMappings.B_to_A, ChronoMappings.A_to_B. 
  apply (fg_rewrite ChronoMappings.map_AB).
Qed.

Lemma AB_fwd_back : forall y, ChronoMappings.A_to_B (ChronoMappings.B_to_A y) = y.
Proof.
  intro y. 
  (* A_to_B (B_to_A y) = forward (backward y) = y by gf_rewrite *)
  unfold ChronoMappings.A_to_B, ChronoMappings.B_to_A.
  apply (gf_rewrite ChronoMappings.map_AB).
Qed.

Lemma BC_back_fwd : forall x, ChronoMappings.C_to_B (ChronoMappings.B_to_C x) = x.
Proof.
  intro x. unfold ChronoMappings.C_to_B, ChronoMappings.B_to_C.
  apply (fg_rewrite ChronoMappings.map_BC).
Qed.

Lemma BC_fwd_back : forall y, ChronoMappings.B_to_C (ChronoMappings.C_to_B y) = y.
Proof.
  intro y. unfold ChronoMappings.B_to_C, ChronoMappings.C_to_B.
  apply (gf_rewrite ChronoMappings.map_BC).
Qed.

Lemma AC_back_fwd : forall x, ChronoMappings.C_to_A (ChronoMappings.A_to_C x) = x.
Proof.
  intro x. unfold ChronoMappings.C_to_A, ChronoMappings.A_to_C.
  apply (fg_rewrite ChronoMappings.map_AC).
Qed.

Lemma AC_fwd_back : forall y, ChronoMappings.A_to_C (ChronoMappings.C_to_A y) = y.
Proof.
  intro y. unfold ChronoMappings.A_to_C, ChronoMappings.C_to_A.
  apply (gf_rewrite ChronoMappings.map_AC).
Qed.

(* Normalization tactic that applies appropriate rewrite rules *)
Ltac normalize_time :=
  repeat (rewrite AB_back_fwd || rewrite AB_fwd_back ||
          rewrite BC_back_fwd || rewrite BC_fwd_back ||
          rewrite AC_back_fwd || rewrite AC_fwd_back);
  try reflexivity.

(* Additional tactical support for composition reasoning *)
Lemma AC_composition_unfold : forall x,
  ChronoMappings.A_to_C x = ChronoMappings.B_to_C (ChronoMappings.A_to_B x).
Proof. 
  intros x. 
  unfold ChronoMappings.A_to_C, ChronoMappings.B_to_C, ChronoMappings.A_to_B.
  unfold forward.
  unfold ChronoMappings.map_AC, ChronoMappings.map_AB, ChronoMappings.map_BC.
  unfold compose_bij.
  reflexivity.
Qed.

Lemma CA_composition_unfold : forall z,
  ChronoMappings.C_to_A z = ChronoMappings.B_to_A (ChronoMappings.C_to_B z).
Proof. 
  intros z. 
  unfold ChronoMappings.C_to_A, ChronoMappings.B_to_A, ChronoMappings.C_to_B.
  unfold backward.
  unfold ChronoMappings.map_AC, ChronoMappings.map_AB, ChronoMappings.map_BC.
  unfold compose_bij.
  reflexivity.
Qed.

(* Tactical hints for automated reasoning *)
Hint Rewrite AB_back_fwd AB_fwd_back : chrono_norm.
Hint Rewrite BC_back_fwd BC_fwd_back : chrono_norm.
Hint Rewrite AC_back_fwd AC_fwd_back : chrono_norm.
Hint Rewrite AC_composition_unfold CA_composition_unfold : chrono_comp.

