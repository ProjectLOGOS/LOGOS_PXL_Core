(* Cross.v - GnosiPraxis cross-pillar theorems *)

From PXLs.Internal Emergent Logics.Pillars.GnosiPraxis Require Import Core.
From PXLs.Internal Emergent Logics.Pillars.ErgoPraxis Require Import Core.
Require Import PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.

Theorem gnosi_cross_ergo (φ : Prop) :
  knowledge_monotone -> hoare_stable -> GnosiPraxis.V φ -> φ.
Proof. intros _ _ H; apply cap_reflect; exact H. Qed.
