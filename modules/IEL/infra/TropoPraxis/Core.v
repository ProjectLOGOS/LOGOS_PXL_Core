From PXLs Require Import PXLv3.
Module TropoPraxis.
  Definition V := PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.TropoPraxis.

  Theorem tropological_reflexivity : forall p, V p -> V p.
  Proof. intros p H. unfold V in H. exact H. Qed.

  Theorem tropological_transitivity : forall p q r, V (p -> q) -> V (q -> r) -> V (p -> r).
  Proof. intros p q r H1 H2. unfold V in *. tauto. Qed.
End TropoPraxis.

(* Exported capabilities *)
Class Cap_TropologicalLogic : Prop := {
  tropological_reflexivity : forall p, TropoPraxis.V p -> TropoPraxis.V p;
  tropological_transitivity : forall p q r, TropoPraxis.V (p -> q) -> TropoPraxis.V (q -> r) -> TropoPraxis.V (p -> r)
}.
Global Instance Cap_TropologicalLogic_inst : Cap_TropologicalLogic := {|
  tropological_reflexivity := TropoPraxis.tropological_reflexivity;
  tropological_transitivity := TropoPraxis.tropological_transitivity
|}.
Export Cap_TropologicalLogic.
