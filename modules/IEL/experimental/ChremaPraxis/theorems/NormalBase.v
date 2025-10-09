From Coq Require Import Program.
(* From PXLs Require Import PXLv3.
Require Import modules.IEL.ChremaPraxis.modal.PhaseSpec. *)
Set Implicit Arguments.

Module ChremaPraxisRules.
  Definition ok := True. Lemma compiles : ok. exact I. Qed.
End ChremaPraxisRules.
