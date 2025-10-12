From Coq Require Import Program String.
From PXLs Require Import PXLv3.
Require Import PXLs.Internal Emergent Logics.Infra.TropoPraxis.Core.
Module TropoPraxis_Registry.
  (* Registry for TropoPraxis infrastructure *)
  Definition core_available : Prop := True.

  Goal core_available.
  Proof. exact I. Qed.
End TropoPraxis_Registry.
