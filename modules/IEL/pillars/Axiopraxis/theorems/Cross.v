(* Cross.v - Axiopraxis cross-pillar theorems *)

From PXLs.Internal Emergent Logics.Pillars.Axiopraxis Require Import Core.
From PXLs.Internal Emergent Logics.Pillars.ThemiPraxis Require Import Core.
Require Import PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.

Theorem axio_cross_themi (φ : Prop) :
  value_monotone -> safe_detachment -> Axiopraxis.V φ -> φ.
Proof. intros _ _ H; apply cap_reflect; exact H. Qed.
