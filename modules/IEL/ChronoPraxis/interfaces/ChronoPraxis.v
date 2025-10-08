(* ChronoPraxis.v - Main Interface Module *)

(* TODO: remove Admitted. — constructive only. No classical axioms. *)

Require Import modules.chronopraxis.substrate.ChronoAxioms
               modules.chronopraxis.substrate.Bijection
               modules.chronopraxis.substrate.ChronoMappings
               modules.chronopraxis.tactics.ChronoTactics
               modules.chronopraxis.theorems.ChronoProofs
               modules.chronopraxis.theorems.MetaTheorems.

Module ChronoPraxis.

(* === Import Core Definitions === *)

Import ChronoAxioms.
Import ChronoMappings.

(* === High-Level Temporal Reasoning Interface === *)

(* Primary temporal reasoning function *)
Definition chrono_reason (e : ChronoAxioms.Eternal) (target_mode : ChronoAxioms.chi) : ChronoAxioms.P_chi target_mode :=
  match target_mode with
  | ChronoAxioms.chi_A => ChronoMappings.project_to_A e
  | ChronoAxioms.chi_B => ChronoMappings.project_to_B e
  | ChronoAxioms.chi_C => ChronoMappings.project_to_C e
  end.

(* Verify temporal reasoning preserves truth *)
Theorem chrono_reason_preserves_truth : 
  forall (e : ChronoAxioms.Eternal) (m : ChronoAxioms.chi),
    match m with
    | ChronoAxioms.chi_A => ChronoMappings.lift_from_A (chrono_reason e ChronoAxioms.chi_A) = e
    | ChronoAxioms.chi_B => ChronoMappings.lift_from_B (chrono_reason e ChronoAxioms.chi_B) = e
    | ChronoAxioms.chi_C => ChronoMappings.lift_from_C (chrono_reason e ChronoAxioms.chi_C) = e
    end.
Proof.
  intros e m.
  destruct m; unfold chrono_reason.
  - apply ChronoMappings.eternal_projection_A.
  - apply ChronoMappings.eternal_projection_B.
  - apply ChronoMappings.eternal_projection_C.
Qed.

(* === Cross-Modal Reasoning === *)

(* Reason across temporal modes using constructive bijections *)
Definition cross_modal_reason (p1 : ChronoAxioms.P_chi ChronoAxioms.chi_A) (target : ChronoAxioms.chi) : 
  match target with
  | ChronoAxioms.chi_A => ChronoAxioms.P_chi ChronoAxioms.chi_A
  | ChronoAxioms.chi_B => ChronoAxioms.P_chi ChronoAxioms.chi_B
  | ChronoAxioms.chi_C => ChronoAxioms.P_chi ChronoAxioms.chi_C
  end :=
  match target with
  | ChronoAxioms.chi_A => p1
  | ChronoAxioms.chi_B => ChronoMappings.A_to_B p1
  | ChronoAxioms.chi_C => ChronoMappings.A_to_C p1
  end.

(* Cross-modal reasoning preserves eternal truth *)
Theorem cross_modal_preservation : 
  forall (p : ChronoAxioms.P_chi ChronoAxioms.chi_A),
    ChronoMappings.lift_from_A p = ChronoMappings.lift_from_B (cross_modal_reason p ChronoAxioms.chi_B) /\
    ChronoMappings.lift_from_A p = ChronoMappings.lift_from_C (cross_modal_reason p ChronoAxioms.chi_C).
Proof.
  intro p.
  unfold cross_modal_reason.
  split.
  - (* A -> B preservation *)
    unfold ChronoMappings.lift_from_A, ChronoMappings.lift_from_B.
    reflexivity.
  - (* A -> C preservation *)  
    unfold ChronoMappings.lift_from_A, ChronoMappings.lift_from_C.
    reflexivity.
Qed.

(* === Main ChronoPraxis Theorem === *)

Theorem chronopraxis_main_theorem : 
  (* All temporal modes are distinct *)
  (ChronoAxioms.chi_A <> ChronoAxioms.chi_B /\ ChronoAxioms.chi_B <> ChronoAxioms.chi_C /\ ChronoAxioms.chi_A <> ChronoAxioms.chi_C) /\
  (* All temporal modes are compatible *)
  (forall m1 m2 : ChronoAxioms.chi, ChronoAxioms.chi_compatible m1 m2) /\
  (* All temporal modes converge on eternal truth *)
  (forall (e : ChronoAxioms.Eternal), 
     ChronoMappings.lift_from_A (ChronoMappings.project_to_A e) = e /\
     ChronoMappings.lift_from_B (ChronoMappings.project_to_B e) = e /\
     ChronoMappings.lift_from_C (ChronoMappings.project_to_C e) = e) /\
  (* ChronoPraxis preserves PXL logical laws *)
  (forall (m : ChronoAxioms.chi) (p : ChronoAxioms.P_chi m), p = p) /\
  (forall (m : ChronoAxioms.chi) (p : ChronoAxioms.P_chi m), ~(p <> p)).
Proof.
  split.
  - (* Distinction *)
    apply ChronoAxioms.chi_distinction.
  - split.
    + (* Compatibility *)
      apply ChronoAxioms.chi_universal_compatibility.
    + split.
      * (* Convergence *)
        intro e.
        split.
        ** apply ChronoMappings.eternal_projection_A.
        ** split.
           *** apply ChronoMappings.eternal_projection_B.
           *** apply ChronoMappings.eternal_projection_C.
      * split.
        ** (* Identity *)
           intros m p.
           apply ChronoAxioms.P_chi_identity.
        ** (* Non-contradiction *)
           intros m p.
           unfold not.
           intro H.
           apply H.
           apply ChronoAxioms.P_chi_identity.
Qed.

(* === Export Core Constructive Theorems === *)
(* Note: These theorems are available from the ConstructiveCore section of ChronoProofs.v *)

End ChronoPraxis.