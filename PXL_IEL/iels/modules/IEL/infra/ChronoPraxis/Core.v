From PXLs Require Import PXLv3.
From PXLs.Internal Emergent Logics.Infra.ChronoPraxis.Theorems Require Import MetaTheorems.
Module ChronoPraxis.
  Definition V := PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.ChronoPraxis.

  Theorem temporal_unification : forall A B C : Prop,
    A -> B -> exists unified_logic : Prop,
      unified_logic = (A /\ B /\ C).
  Proof. apply ChronoPraxis_MetaTheorems.temporal_unification_meta. Qed.

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
Export Cap_TemporalLogic.
