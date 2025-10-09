From Coq Require Import Program.
(* From PXLs Require Import PXLv3.
Require Import modules.IEL.MuPraxis.modal.FixSpec. *)
Set Implicit Arguments.

Module MuRules.
  Definition ok := True. Lemma compiles : ok. exact I. Qed.
End MuRules.
