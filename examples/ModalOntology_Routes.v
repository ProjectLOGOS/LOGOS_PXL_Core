(* ModalOntology_Routes.v - Concrete example of modal accessibility *)

From Coq Require Import Program.

(* TODO: Restore full imports once module path resolution is fixed *)
(* Require Import PXLs.IEL.Infra.substrate.ChronoAxioms *)
(*                PXLs.IEL.Infra.substrate.ChronoMappings *)
(*                PXLs.IEL.Infra.domains.ModalOntology.ModalCollapse. *)

Module Routes.

(* Simplified temporal types for the example *)
Parameter PA : Type.  (* χ_A - lived time propositions *)
Parameter PC : Type.  (* χ_C - eternal time propositions *)
Parameter A_to_C : PA -> PC.

(* Simplified modal accessibility *)
Definition Access (pC qC : PC) : Prop := 
  exists pA, A_to_C pA = pC /\ A_to_C pA = qC.

(* Example scenario: different routes to work *)
(* Route A: Take highway *)
Parameter pA_highway : PA.

(* Route B: Take side streets *)
Parameter pA_streets : PA.

(* Both routes lead to same eternal outcome: "arrived at work" *)
Parameter pC_work : PC.

Parameter highway_arrives : A_to_C pA_highway = pC_work.
Parameter streets_arrive : A_to_C pA_streets = pC_work.

(* Key theorem: The eternal outcome is accessible from itself *)
(* This captures modal collapse - all paths through lived time *)
(* that reach the same eternal state make that state self-accessible *)
Theorem route_accessibility : Access pC_work pC_work.
Proof.
  exists pA_highway.
  split.
  - exact highway_arrives.  (* Highway gets us to work *)
  - exact highway_arrives.  (* Same eternal outcome *)
Qed.

(* Alternative proof using the other route *)
Theorem route_accessibility_alt : Access pC_work pC_work.
Proof.
  exists pA_streets.
  split.
  - exact streets_arrive.   (* Streets get us to work *)
  - exact streets_arrive.   (* Same eternal outcome *)
Qed.

(* Path insensitivity: doesn't matter which route we consider *)
(* The eternal state "arrived at work" is accessible because *)
(* lived experience (either route) can reach it *)

(* More complex example: considering multiple destinations *)
Parameter pC_home pC_store : PC.
Parameter pA_home_direct pA_store_via_home : PA.

Parameter home_direct : A_to_C pA_home_direct = pC_home.
Parameter store_detour : A_to_C pA_store_via_home = pC_store.

(* Different eternal outcomes are not accessible from each other *)
(* (unless there's a lived experience connecting them) *)
Parameter distinct_outcomes : pC_home <> pC_store.

(* Home is accessible to itself *)
Theorem home_self_accessible : Access pC_home pC_home.
Proof.
  exists pA_home_direct.
  split; exact home_direct.
Qed.

(* But home and store are not accessible to each other *)
(* (given our current lived experience options) *)
Theorem home_store_not_accessible : ~ Access pC_home pC_store.
Proof.
  intro H.
  destruct H as [pA [H1 H2]].
  (* If pA maps to both home and store, they'd be equal *)
  (* But we know they're distinct *)
  rewrite H1 in H2.
  exact (distinct_outcomes H2).
Qed.

End Routes.
