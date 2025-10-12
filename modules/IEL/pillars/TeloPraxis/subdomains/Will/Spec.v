From PXLs Require Import PXLv3.
Require Import PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.
Module WillSub.
  Import TheoProps.

  Context `{Cap_EndMonotone Will} `{Cap_VolitionalLift Will} `{Cap_ReflectsPXL Will}.

  Definition V := Will.

  Theorem conservative : forall p, V p -> p.
  Proof. apply cap_reflect. Qed.

  Theorem end_monotone : forall p q, (p -> q) -> Will p -> Will q.
  Proof. apply cap_em. Qed.

  Theorem volitional_lift : forall p, Will p -> Box Will p.
  Proof. apply cap_vl. Qed.
End WillSub.
