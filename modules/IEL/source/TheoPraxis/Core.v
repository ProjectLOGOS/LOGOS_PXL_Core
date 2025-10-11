From Coq Require Import Program String Init.Datatypes.
From PXLs Require Import PXLv3.
From PXLs.IEL.Source.TheoPraxis Require Import Props.
Require Import PXLs.IEL.Source.TheoPraxis.subdomains.Unity.Spec.
Import Init.Datatypes.
Open Scope string_scope.
Module TheoPraxis.
  Import TheoProps UnitySpec.

  Definition V := TheoProps.Truth.

  Theorem unity_foundation : forall p, V p -> p.
  Proof. apply truth_reflect. Qed.

  Theorem theological_consistency : forall p q, V p -> V q -> V (p /\ q).
  Proof. intros p q H1 H2. unfold V in *. split; assumption. Qed.

  Theorem ontological_unity : "Unity" = "Unity".
  Proof. reflexivity. Qed.
End TheoPraxis.

(* Exported capabilities *)
Class Cap_TheologicalFoundation : Prop := {
  unity_foundation : forall p, TheoPraxis.V p -> p;
  theological_consistency : forall p q, TheoPraxis.V p -> TheoPraxis.V q -> TheoPraxis.V (p /\ q);
  ontological_unity : UnitySpec.prop_name = "Unity"
}.
Global Instance Cap_TheologicalFoundation_inst : Cap_TheologicalFoundation := {|
  unity_foundation := TheoPraxis.unity_foundation;
  theological_consistency := TheoPraxis.theological_consistency;
  ontological_unity := TheoPraxis.ontological_unity
|}.