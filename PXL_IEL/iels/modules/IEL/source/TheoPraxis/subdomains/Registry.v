From Coq Require Import Program String Init.Datatypes.
From PXLs Require Import PXLv3.
Require Import PXLs.Internal Emergent Logics.Source.TheoPraxis.subdomains.Unity.Spec.
Import Init.Datatypes.
Open Scope string_scope.
Module TheoPraxis_OntoProps.
  (* name -> (pillar, c_value) *)
  Definition registry : list (string * string * string) := cons ("Unity", UnitySpec.pillar, UnitySpec.c_value) nil.
  Goal True. exact I. Qed.
End TheoPraxis_OntoProps.
