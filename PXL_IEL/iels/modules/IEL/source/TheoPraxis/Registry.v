From Coq Require Import Program String.
From PXLs Require Import PXLv3.
Require Import PXLs.Internal Emergent Logics.Source.TheoPraxis.Core.
Module TheoPraxis_Registry.
  (* Registry for TheoPraxis source foundation *)
  Definition core_available : Prop := True.

  Goal core_available.
  Proof. exact I. Qed.
End TheoPraxis_Registry.
