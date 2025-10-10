(* ChronoMappings.v - PXL Canonical Bijective Mappings *)

From Coq Require Import Program.
From PXLs.IEL.Infra.ChronoPraxis.Substrate Require Import ChronoAxioms.
From PXLs.IEL.Infra.ChronoPraxis.Substrate Require Import Bijection.

Set Implicit Arguments.
Set Primitive Projections.

Module ChronoMappings.

(* === Constructive Bijections Between Temporal Modes === *)

(* Forward/backward function parameters *)
Parameter map_A_to_B : ChronoAxioms.P_chi ChronoAxioms.chi_A -> ChronoAxioms.P_chi ChronoAxioms.chi_B.
Parameter map_B_to_A : ChronoAxioms.P_chi ChronoAxioms.chi_B -> ChronoAxioms.P_chi ChronoAxioms.chi_A.
Parameter map_B_to_C : ChronoAxioms.P_chi ChronoAxioms.chi_B -> ChronoAxioms.P_chi ChronoAxioms.chi_C.
Parameter map_C_to_B : ChronoAxioms.P_chi ChronoAxioms.chi_C -> ChronoAxioms.P_chi ChronoAxioms.chi_B.
Parameter map_A_to_C : ChronoAxioms.P_chi ChronoAxioms.chi_A -> ChronoAxioms.P_chi ChronoAxioms.chi_C.
Parameter map_C_to_A : ChronoAxioms.P_chi ChronoAxioms.chi_C -> ChronoAxioms.P_chi ChronoAxioms.chi_A.

(* Constructive hypotheses for bijection properties *)
Parameter map_AB_sect : forall p, map_B_to_A (map_A_to_B p) = p.
Parameter map_AB_retr : forall p, map_A_to_B (map_B_to_A p) = p.
Parameter map_BC_sect : forall p, map_C_to_B (map_B_to_C p) = p.
Parameter map_BC_retr : forall p, map_B_to_C (map_C_to_B p) = p.
Parameter map_AC_sect : forall p, map_C_to_A (map_A_to_C p) = p.
Parameter map_AC_retr : forall p, map_A_to_C (map_C_to_A p) = p.

(* Constructive bijections between modes *)
Definition map_AB : Bijection (ChronoAxioms.P_chi ChronoAxioms.chi_A)
                              (ChronoAxioms.P_chi ChronoAxioms.chi_B).
Proof.
  refine {| f := map_A_to_B; g := map_B_to_A |}.
  - (* gf: g (f x) = x *) intro x. apply map_AB_sect.
  - (* fg: f (g y) = y *) intro y. apply map_AB_retr.
Defined.

Definition map_BC : Bijection (ChronoAxioms.P_chi ChronoAxioms.chi_B)
                              (ChronoAxioms.P_chi ChronoAxioms.chi_C).
Proof.
  refine {| f := map_B_to_C; g := map_C_to_B |}.
  - (* gf: g (f x) = x *) intro x. apply map_BC_sect.
  - (* fg: f (g y) = y *) intro y. apply map_BC_retr.
Defined.

(* Prefer composition for AC to stay purely constructive *)
Definition map_AC : Bijection (ChronoAxioms.P_chi ChronoAxioms.chi_A)
                              (ChronoAxioms.P_chi ChronoAxioms.chi_C) :=
  compose_bij map_AB map_BC.

(* Export canonical forward/backward maps *)
Definition A_to_B := forward map_AB.
Definition B_to_A := backward map_AB.
Definition B_to_C := forward map_BC.
Definition C_to_B := backward map_BC.
Definition A_to_C := forward map_AC.
Definition C_to_A := backward map_AC.

(* === Eternal-Temporal Projection/Lifting === *)

(* Project eternal propositions into temporal modes *)
Parameter project_to_A : ChronoAxioms.Eternal -> ChronoAxioms.P_chi ChronoAxioms.chi_A.
Parameter project_to_B : ChronoAxioms.Eternal -> ChronoAxioms.P_chi ChronoAxioms.chi_B.
Parameter project_to_C : ChronoAxioms.Eternal -> ChronoAxioms.P_chi ChronoAxioms.chi_C.

(* Lift temporal propositions to eternal domain *)
Parameter lift_from_A : ChronoAxioms.P_chi ChronoAxioms.chi_A -> ChronoAxioms.Eternal.
Parameter lift_from_B : ChronoAxioms.P_chi ChronoAxioms.chi_B -> ChronoAxioms.Eternal.
Parameter lift_from_C : ChronoAxioms.P_chi ChronoAxioms.chi_C -> ChronoAxioms.Eternal.

(* === Bijection Preservation - REMOVED === *)

End ChronoMappings.


