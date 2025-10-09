(* Cross.v - Axiopraxis cross-pillar theorems *)

From PXLs.IEL.Pillars.Axiopraxis Require Import Core.
From PXLs.IEL.Pillars.ThemiPraxis Require Import Core.
Require Import PXLs.IEL.Source.TheoPraxis.Props.

Theorem axio_cross_themi (φ : Prop) :
  value_monotone -> safe_detachment -> Axiopraxis.V φ -> φ.
Proof. intros _ _ H; apply cap_reflect; exact H. Qed.
