From Coq Require Import QArith Program.
(* From PXLs Require Import PXLv3.
Require Import modules.IEL.TychePraxis.modal.ProbSpec. *)
Set Implicit Arguments.

Module TycheRules.
  Definition ok := True. Lemma compiles : ok. exact I. Qed.
End TycheRules.
