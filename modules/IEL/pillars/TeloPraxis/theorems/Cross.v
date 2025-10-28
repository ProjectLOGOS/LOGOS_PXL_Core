(* Cross.v - TeloPraxis cross-pillar theorems *)

From PXLs.IEL.Pillars.TeloPraxis Require Import Core.
From PXLs.IEL.Pillars.AnthroPraxis Require Import Core.
Require Import PXLs.IEL.Source.TheoPraxis.Props.

Theorem telo_cross_anthro (φ : Prop) :
  end_monotone -> agency_compat -> TeloPraxis.V φ -> φ.
Proof. intros _ _ H; apply cap_reflect; exact H. Qed.
