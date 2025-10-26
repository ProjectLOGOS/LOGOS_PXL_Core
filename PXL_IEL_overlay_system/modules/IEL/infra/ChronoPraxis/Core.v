From PXLs Require Import PXLv3.
Module ChronoPraxis.
  Definition V := PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.ChronoPraxis.

  Theorem temporal_unification : forall A B C : Prop,
    A -> B -> exists unified_logic : Prop,
      unified_logic = (A /\ B /\ C).
  Proof.
    intros A B C HA HB.
    exists (A /\ B /\ C).
    reflexivity.
  Qed.
  Theorem constructive_completeness : forall P : Prop,
    ~ (P /\ ~ P).
  Proof. intros P [HP HnP]. contradiction. Qed.
End ChronoPraxis.

(* Exported capabilities *)
Class Cap_TemporalLogic : Prop := {
  temporal_unification : forall A B C : Prop,
    A -> B -> exists unified_logic : Prop,
      unified_logic = (A /\ B /\ C)
}.
Global Instance Cap_TemporalLogic_inst : Cap_TemporalLogic := {|
  temporal_unification := ChronoPraxis.temporal_unification
|}.
