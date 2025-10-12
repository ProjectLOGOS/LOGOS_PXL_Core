From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.Internal Emergent Logics.CosmoPraxis.subdomains.Immanence.Spec.
Module CosmoPraxis_OntoProps.
  (* name -> (pillar, c_value) *)
  Definition registry : list (string * string * string) := [
  ("Immanence", ImmanenceSpec.pillar, ImmanenceSpec.c_value)
  ].
  Goal True. exact I. Qed.
End CosmoPraxis_OntoProps.
