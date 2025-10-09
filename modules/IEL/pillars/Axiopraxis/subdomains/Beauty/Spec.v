From PXLs Require Import PXLv3.
From PXLs.IEL.Source.TheoPraxis Require Import Props.
Module BeautySub.
  Import TheoProps.
  Context `{Cap_ConjElim Beauty} `{Cap_ReflectsPXL Beauty}.
  Definition V := Beauty.
  Theorem conservative : forall p, V p -> p.
  Proof. apply cap_reflect. Qed.
  Theorem conj_elim : forall p q, Beauty (p /\ q) -> Beauty p /\ Beauty q.
  Proof. intros; apply cap_ce; assumption. Qed.
End BeautySub.
