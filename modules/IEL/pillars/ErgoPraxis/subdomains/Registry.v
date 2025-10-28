From Coq Require Import Program String.
From PXLs Require Import PXLv3.
Require Import PXLs.IEL.Pillars.ErgoPraxis.subdomains.Truth.Spec.
Module ErgoPraxis_Registry.
  (* Registry for ErgoPraxis subdomains *)
  Definition truth_available : Prop := True.

  Goal truth_available.
  Proof. exact I. Qed.
End ErgoPraxis_Registry.