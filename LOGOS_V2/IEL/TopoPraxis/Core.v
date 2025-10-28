From PXLs Require Import PXLv3.
Module TopoPraxis.
  Definition V := PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.TopoPraxis.

  Theorem topological_continuity : forall p q, V p -> V q -> V (p /\ q).
  Proof. intros p q H1 H2. unfold V in *. tauto. Qed.

  Theorem topological_separation : forall p, V p -> V (~ p) -> False.
  Proof. intros p H1 H2. unfold V in *. tauto. Qed.
End TopoPraxis.

(* Exported capabilities *)
Class Cap_TopologicalLogic : Prop := {
  topological_continuity : forall p q, TopoPraxis.V p -> TopoPraxis.V q -> TopoPraxis.V (p /\ q);
  topological_separation : forall p, TopoPraxis.V p -> TopoPraxis.V (~ p) -> False
}.
Global Instance Cap_TopologicalLogic_inst : Cap_TopologicalLogic := {|
  topological_continuity := TopoPraxis.topological_continuity;
  topological_separation := TopoPraxis.topological_separation
|}.
Export Cap_TopologicalLogic.
