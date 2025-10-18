From Coq Require Import Program String.
From PXLs Require Import PXLv3.
Require Import PXLs.Internal Emergent Logics.Pillars.ThemiPraxis.subdomains.Truth.Spec.
Module ThemiPraxis_Registry.
  (* Registry for ThemiPraxis subdomains *)
  Definition truth_available : Prop := True.

  Goal truth_available.
  Proof. exact I. Qed.
End ThemiPraxis_Registry.
