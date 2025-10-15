From PXLs Require Import PXLv3.
Require Import PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.
Module TruthSub.
  Import TheoProps.

  Context `{Cap_ValueMonotone Truth} `{Cap_NonExplosion Truth} `{Cap_ReflectsPXL Truth}.

  Definition V := Truth.

  Theorem conservative : forall φ, V φ -> φ.
  Proof. apply cap_reflect. Qed.

  Theorem monotone : forall p q, (p -> q) -> Truth p -> Truth q.
  Proof. intros; eapply cap_vm; eauto. Qed.

  Theorem non_explosion : ~ Truth False.
  Proof. apply cap_ne. Qed.
End TruthSub.
