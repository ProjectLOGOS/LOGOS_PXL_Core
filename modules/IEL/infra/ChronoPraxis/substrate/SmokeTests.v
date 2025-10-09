(* Simple smoke test that can be compiled in the chronopraxis directory *)
Require Import ChronoAxioms.
Require Import Bijection.
Require Import ChronoMappings.
Require Import ChronoProofs.

Set Implicit Arguments.

Notation PA := (ChronoAxioms.P_chi ChronoAxioms.chi_A).
Notation PB := (ChronoAxioms.P_chi ChronoAxioms.chi_B).
Notation PC := (ChronoAxioms.P_chi ChronoAxioms.chi_C).

Section SmokeTests.
Variable pA : PA. Variable pB : PB. Variable pC : PC.

(* Test basic bijection properties directly *)
Lemma test_collapse_A : ChronoMappings.B_to_A (ChronoMappings.A_to_B pA) = pA.
Proof. 
  unfold ChronoMappings.B_to_A, ChronoMappings.A_to_B.
  unfold backward, forward.
  apply (fg ChronoMappings.map_AB).
Qed.

Lemma test_collapse_B : ChronoMappings.A_to_B (ChronoMappings.B_to_A pB) = pB.
Proof. 
  unfold ChronoMappings.A_to_B, ChronoMappings.B_to_A.
  unfold forward, backward.
  apply (gf ChronoMappings.map_AB).
Qed.

Lemma test_collapse_C : ChronoMappings.B_to_C (ChronoMappings.C_to_B pC) = pC.
Proof. 
  unfold ChronoMappings.B_to_C, ChronoMappings.C_to_B.
  unfold forward, backward.
  apply (gf ChronoMappings.map_BC).
Qed.

(* Test that constructive core theorems from ChronoProofs are available *)
Lemma test_temporal_convergence_available : ChronoMappings.C_to_A (ChronoMappings.A_to_C pA) = pA.
Proof. apply temporal_convergence. Qed.

Lemma test_chronological_collapse_available : ChronoMappings.B_to_A (ChronoMappings.A_to_B pA) = pA.
Proof. apply chronological_collapse_A. Qed.

End SmokeTests.
