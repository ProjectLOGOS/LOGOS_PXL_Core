From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.Internal Emergent Logics.TeloPraxis.subdomains.Will.Spec.
Module TeloPraxis_OntoProps.
  (* name -> (pillar, c_value) *)
  Definition registry : list (string * string * string) := [
  ("Will", WillSpec.pillar, WillSpec.c_value)
  ].
  Goal True. exact I. Qed.
End TeloPraxis_OntoProps.
