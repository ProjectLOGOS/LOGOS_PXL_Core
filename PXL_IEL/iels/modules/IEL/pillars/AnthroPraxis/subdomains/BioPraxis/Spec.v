From PXLs Require Import PXLv3.
Require Import PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.
Module BioPraxisSub.
  Import TheoProps.

  Definition V := BioPraxis.

  Theorem conservative : forall p, V p -> p.
  Proof. apply cap_reflect. Qed.

  Theorem agent_capability : forall p, BioPraxis p -> Dia_Prop (BioPraxis p).
  Proof. apply cap_ac. Qed.

  Theorem agency_comp : forall p q, BioPraxis p -> BioPraxis q -> BioPraxis (p /\ q).
  Proof. apply cap_ag. Qed.
End BioPraxisSub.
