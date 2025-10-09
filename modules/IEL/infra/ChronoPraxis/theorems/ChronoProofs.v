(* ChronoProofs.v - PXL Canonical Constructive Proofs *)

(* TODO: remove Admitted. — constructive only. No classical axioms. *)

Require Import modules.chronopraxis.substrate.ChronoAxioms
               modules.chronopraxis.substrate.Bijection
               modules.chronopraxis.substrate.ChronoMappings
               modules.chronopraxis.tactics.ChronoTactics.

From PXLs.IEL.Infra.ChronoPraxis Require Import Core.

Module ChronoProofs.

Import ChronoAxioms.
Import ChronoMappings.

(* === Core Identity Preservation === *)

(* Temporal mode identity is reflexive *)
Theorem chi_identity_preservation `{Cap_ChiReflexive ChronoAxioms.chi (@eq ChronoAxioms.chi)} : forall m : ChronoAxioms.chi, m = m.
Proof.
  intro m.
  apply chi_refl.
Qed.

(* Proposition identity within temporal modes *)
Theorem P_chi_identity_preservation : forall (m : ChronoAxioms.chi) (p : ChronoAxioms.P_chi m), p = p.
Proof.
  intros m p.
  apply ChronoAxioms.ChronoAxioms.P_chi_identity.
Qed.

(* ChronoAxioms.Eternal proposition identity *)
Theorem eternal_identity_preservation : forall (e : ChronoAxioms.Eternal), e = e.
Proof.
  intro e.
  apply ChronoAxioms.eternal_timeless.
Qed.

(* === Bijective Mapping Soundness === *)

(* Soundness: ChronoAxioms.Eternal -> temporal -> ChronoAxioms.Eternal preserves identity *)
Theorem eternal_temporal_soundness_A : 
  forall (e : ChronoAxioms.Eternal), ChronoMappings.lift_from_A (ChronoMappings.project_to_A e) = e.
Proof.
  intro e.
  apply ChronoMappings.eternal_projection_A.
Qed.

Theorem eternal_temporal_soundness_B : 
  forall (e : ChronoAxioms.Eternal), ChronoMappings.lift_from_B (ChronoMappings.project_to_B e) = e.
Proof.
  intro e.
  apply ChronoMappings.eternal_projection_B.
Qed.

Theorem eternal_temporal_soundness_C : 
  forall (e : ChronoAxioms.Eternal), ChronoMappings.lift_from_C (ChronoMappings.project_to_C e) = e.
Proof.
  intro e.
  apply ChronoMappings.eternal_projection_C.
Qed.

(* Completeness: temporal -> ChronoAxioms.Eternal -> temporal preserves identity *)
Theorem temporal_eternal_completeness_A : 
  forall (p : ChronoAxioms.P_chi ChronoAxioms.chi_A), ChronoMappings.project_to_A (ChronoMappings.lift_from_A p) = p.
Proof.
  intro p.
  apply ChronoMappings.temporal_lifting_A.
Qed.

Theorem temporal_eternal_completeness_B : 
  forall (p : ChronoAxioms.P_chi ChronoAxioms.chi_B), ChronoMappings.project_to_B (ChronoMappings.lift_from_B p) = p.
Proof.
  intro p.
  apply ChronoMappings.temporal_lifting_B.
Qed.

Theorem temporal_eternal_completeness_C : 
  forall (p : ChronoAxioms.P_chi ChronoAxioms.chi_C), ChronoMappings.project_to_C (ChronoMappings.lift_from_C p) = p.
Proof.
  intro p.
  apply ChronoMappings.temporal_lifting_C.
Qed.

(* === Cross-Mode Bijection Proofs === *)

(* Cross-mode mappings are bijective *)
Theorem cross_mode_bijection_AB : 
  forall (p : ChronoAxioms.P_chi ChronoAxioms.chi_A), ChronoMappings.B_to_A (ChronoMappings.A_to_B p) = p.
Proof.
  intro p.
  apply ChronoMappings.cross_mapping_consistency_AB.
Qed.

Theorem cross_mode_bijection_BA : 
  forall (p : ChronoAxioms.P_chi ChronoAxioms.chi_B), ChronoMappings.A_to_B (ChronoMappings.B_to_A p) = p.
Proof.
  intro p.
  apply ChronoMappings.cross_mapping_consistency_BA.
Qed.

(* === Temporal Convergence Theorems === *)

(* Convergence: All temporal modes resolve to same ChronoAxioms.Eternal truth *)
Definition temporal_convergence_formula (e : ChronoAxioms.Eternal) : Prop :=
  ChronoMappings.lift_from_A (ChronoMappings.project_to_A e) = e /\
  ChronoMappings.lift_from_B (ChronoMappings.project_to_B e) = e /\
  ChronoMappings.lift_from_C (ChronoMappings.project_to_C e) = e.

Theorem universal_temporal_convergence : 
  forall (e : ChronoAxioms.Eternal), temporal_convergence_formula e.
Proof.
  intro e.
  unfold temporal_convergence_formula.
  split.
  - apply ChronoMappings.eternal_projection_A.
  - split.
    + apply ChronoMappings.eternal_projection_B.
    + apply ChronoMappings.eternal_projection_C.
Qed.

(* === Triune Unity Theorem === *)
(* This is the central theorem proving A/B/C theory compatibility *)

Theorem triune_temporal_unity : 
  forall (e : ChronoAxioms.Eternal),
    ChronoMappings.lift_from_A (ChronoMappings.project_to_A e) = 
    ChronoMappings.lift_from_B (ChronoMappings.project_to_B e) /\
    ChronoMappings.lift_from_B (ChronoMappings.project_to_B e) = 
    ChronoMappings.lift_from_C (ChronoMappings.project_to_C e).
Proof.
  intro e.
  split.
  - (* A-mode and B-mode converge *)
    rewrite ChronoMappings.eternal_projection_A.
    rewrite ChronoMappings.eternal_projection_B.
    reflexivity.
  - (* B-mode and C-mode converge *)
    rewrite ChronoMappings.eternal_projection_B.
    rewrite ChronoMappings.eternal_projection_C.
    reflexivity.
Qed.

(* === Chronological Collapse Prevention === *)
(* Proves that temporal modes remain distinct despite convergence *)

Theorem chronological_non_collapse : 
  ChronoAxioms.chi_A <> ChronoAxioms.chi_B /\ ChronoAxioms.chi_B <> ChronoAxioms.chi_C /\ ChronoAxioms.chi_A <> ChronoAxioms.chi_C.
Proof.
  apply ChronoAxioms.chi_distinction.
Qed.

(* === Temporal Resolution Soundness === *)
(* Mapping between temporal states preserves logical identity *)

Theorem temporal_resolution_soundness : 
  forall (e : ChronoAxioms.Eternal),
    ChronoMappings.lift_from_A (ChronoMappings.project_to_A e) = e /\
    ChronoMappings.lift_from_B (ChronoMappings.project_to_B e) = e /\
    ChronoMappings.lift_from_C (ChronoMappings.project_to_C e) = e.
Proof.
  intro e.
  split.
  - apply ChronoMappings.eternal_projection_A.
  - split.
    + apply ChronoMappings.eternal_projection_B.
    + apply ChronoMappings.eternal_projection_C.
Qed.

(* === Main Constructive Theorem === *)
(* ChronoPraxis preserves PXL's fundamental logical laws *)

Theorem chronopraxis_preserves_PXL_constructive :
  (* Identity Law *)
  (forall (m : ChronoAxioms.chi) (p : ChronoAxioms.P_chi m), p = p) /\
  (* Non-Contradiction Law *)
  (forall (m : ChronoAxioms.chi) (p : ChronoAxioms.P_chi m), ~(p <> p)).
Proof.
  split.
  - (* Identity *)
    intros m p.
    apply ChronoAxioms.P_chi_identity.
  - (* Non-Contradiction *)
    intros m p.
    unfold not.
    intro H.
    apply H.
    apply ChronoAxioms.P_chi_identity.
Qed.

(* === Constructive Temporal Convergence === *)
(* This will be replaced by the constructive version in the new section *)

(* === Alternative Constructive Convergence === *)
(* A weaker but provable convergence property *)

Theorem bijection_round_trip_convergence :
  forall (pA : ChronoAxioms.P_chi ChronoAxioms.chi_A),
    ChronoMappings.B_to_A (ChronoMappings.A_to_B pA) = pA /\
    ChronoMappings.A_to_B (ChronoMappings.B_to_A (ChronoMappings.A_to_B pA)) = ChronoMappings.A_to_B pA.
Proof.
  intro pA.
  split.
  - (* B_to_A (A_to_B pA) = pA *)
    unfold ChronoMappings.A_to_B, ChronoMappings.B_to_A.
    apply ChronoMappings.map_AB.(fg).
  - (* A_to_B (B_to_A (A_to_B pA)) = A_to_B pA *)
    unfold ChronoMappings.A_to_B, ChronoMappings.B_to_A.
    rewrite ChronoMappings.map_AB.(fg).
    reflexivity.
Qed.

End ChronoProofs.

(* ================================================================ *)
From Coq Require Import Program.

Set Implicit Arguments.

Section ConstructiveCore.

(* Shorthands for types of propositions in each mode *)
Notation PA := (ChronoAxioms.P_chi ChronoAxioms.chi_A).
Notation PB := (ChronoAxioms.P_chi ChronoAxioms.chi_B).
Notation PC := (ChronoAxioms.P_chi ChronoAxioms.chi_C).

(* Alias for inverse bijection *)
Definition sym_bij {X Y : Type} (bij : Bijection X Y) : Bijection Y X := inverse_bij bij.

(* 1) Temporal convergence via round trip through C should return to original *)
Theorem temporal_convergence :
  forall pA : PA,
    ChronoMappings.C_to_A (ChronoMappings.A_to_C pA) = pA.
Proof. 
  intro pA. 
  (* Round trip through A→C→A should be identity by bijection property *)
  unfold ChronoMappings.A_to_C, ChronoMappings.C_to_A.
  unfold forward, backward.
  apply (fg ChronoMappings.map_AC).
Qed.

(* 2) Chronological collapse: round trips are identities in all modes *)
Theorem chronological_collapse_A : forall pA:PA, (ChronoMappings.B_to_A (ChronoMappings.A_to_B pA)) = pA.
Proof. 
  intro pA. 
  unfold ChronoMappings.B_to_A, ChronoMappings.A_to_B, backward, forward.
  apply (fg ChronoMappings.map_AB).
Qed.

Theorem chronological_collapse_B : forall pB:PB, (ChronoMappings.A_to_B (ChronoMappings.B_to_A pB)) = pB.
Proof. 
  intro pB. 
  unfold ChronoMappings.A_to_B, ChronoMappings.B_to_A, forward, backward.
  apply (gf ChronoMappings.map_AB).
Qed.

Theorem chronological_collapse_C : forall pC:PC, (ChronoMappings.B_to_C (ChronoMappings.C_to_B pC)) = pC.
Proof. 
  intro pC. 
  unfold ChronoMappings.B_to_C, ChronoMappings.C_to_B, forward, backward.
  apply (gf ChronoMappings.map_BC).
Qed.

(* 3) Causal bijection: composition A→B→C is a bijection with inverse C→B→A *)
Definition bij_A_to_C : Bijection PA PC := ChronoMappings.map_AC.
Definition bij_C_to_A : Bijection PC PA := sym_bij ChronoMappings.map_AC.

Theorem causal_bijection_forward :
  forall pA, ChronoMappings.C_to_A (ChronoMappings.A_to_C pA) = pA.
Proof. 
  intro pA. 
  (* This is just the temporal_convergence theorem *)
  apply temporal_convergence.
Qed.

Theorem causal_bijection_backward :
  forall pC, ChronoMappings.A_to_C (ChronoMappings.C_to_A pC) = pC.
Proof. 
  intro pC.
  unfold ChronoMappings.A_to_C, ChronoMappings.C_to_A.
  unfold forward, backward.
  apply (gf ChronoMappings.map_AC).
Qed.

(* 4) Temporal consistency: any two A→C paths via B are equal *)
Theorem temporal_consistency :
  forall pA : PA,
    ChronoMappings.A_to_C pA = (ChronoMappings.B_to_C (ChronoMappings.A_to_B pA)) /\ 
    ChronoMappings.A_to_C pA = (ChronoMappings.A_to_C pA).
Proof.
  intro pA.
  split.
  - (* A→C equals A→B→C - by definition since map_AC := compose_bij map_AB map_BC *)
    unfold ChronoMappings.A_to_C, ChronoMappings.B_to_C, ChronoMappings.A_to_B.
    unfold ChronoMappings.map_AC. 
    reflexivity.
  - reflexivity.
Qed.

(* Quick smoketest lemmas (ensure rewrite works across contexts) *)  
Lemma ac_eq_bc (pA:PA) : ChronoMappings.A_to_C pA = ChronoMappings.B_to_C (ChronoMappings.A_to_B pA).
Proof. 
  (* By definition since map_AC := compose_bij map_AB map_BC *)
  unfold ChronoMappings.A_to_C, ChronoMappings.B_to_C, ChronoMappings.A_to_B.
  unfold ChronoMappings.map_AC. 
  reflexivity.
Qed.

End ConstructiveCore.
