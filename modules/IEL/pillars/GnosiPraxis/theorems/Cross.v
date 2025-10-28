(* Cross.v - GnosiPraxis cross-pillar theorems *)

From PXLs.IEL.Pillars.GnosiPraxis Require Import Core.
From PXLs.IEL.Pillars.ErgoPraxis Require Import Core.
Require Import PXLs.IEL.Source.TheoPraxis.Props.

Theorem gnosi_cross_ergo (φ : Prop) :
  knowledge_monotone -> hoare_stable -> GnosiPraxis.V φ -> φ.
Proof. intros _ _ H; apply cap_reflect; exact H. Qed.
