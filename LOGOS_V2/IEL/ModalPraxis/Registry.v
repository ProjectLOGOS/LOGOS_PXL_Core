From Coq Require Import Program String.
From PXLs Require Import PXLv3.
Require Import PXLs.Internal Emergent Logics.Infra.ModalPraxis.Core.
Module ModalPraxis_Registry.
  (* Registry for ModalPraxis infrastructure *)
  Definition core_available : Prop := True.

  Goal core_available.
  Proof. exact I. Qed.
End ModalPraxis_Registry.
