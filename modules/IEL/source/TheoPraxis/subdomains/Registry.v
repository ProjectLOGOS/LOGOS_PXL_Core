From Coq Require Import Program.
From PXLs Require Import PXLv3.
Require Import modules.IEL.TheoPraxis.subdomains.Unity.Spec.
Module TheoPraxis_OntoProps.
  (* name -> (pillar, c_value) *)
  Definition registry : list (string * string * string) := [
  ("Unity", UnitySpec.pillar, UnitySpec.c_value)
  ].
  Goal True. exact I. Qed.
End TheoPraxis_OntoProps.
