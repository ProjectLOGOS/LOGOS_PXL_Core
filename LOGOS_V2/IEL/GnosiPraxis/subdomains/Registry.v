From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.Internal Emergent Logics.GnosiPraxis.subdomains.Truth.Spec.
Module GnosiPraxis_OntoProps.
  (* name -> (pillar, c_value) *)
  Definition registry : list (string * string * string) := [
  ("Truth", TruthSpec.pillar, TruthSpec.c_value)
  ].
  Goal True. exact I. Qed.
End GnosiPraxis_OntoProps.
