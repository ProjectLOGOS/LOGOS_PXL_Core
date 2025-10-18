(* Cross.v - TeloPraxis cross-pillar theorems *)

From PXLs.Internal Emergent Logics.Pillars.TeloPraxis Require Import Core.
From PXLs.Internal Emergent Logics.Pillars.AnthroPraxis Require Import Core.
Require Import PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.

Theorem telo_cross_anthro (φ : Prop) :
  end_monotone -> agency_compat -> TeloPraxis.V φ -> φ.
Proof. intros _ _ H; apply cap_reflect; exact H. Qed.
