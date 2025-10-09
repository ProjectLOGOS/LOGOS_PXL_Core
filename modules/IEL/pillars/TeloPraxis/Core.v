From PXLs.IEL.Pillars.TeloPraxis.subdomains Require Import Will.Spec.
Module TeloPraxis.
  Definition V := PXLs.IEL.Source.TheoPraxis.Props.Will.
  Theorem EndMonotone : forall p q, (p -> q) -> V p -> V q.
  Proof. apply WillSub.end_monotone. Qed.
  Theorem VolitionalLift : forall p, V p -> Box V p.
  Proof. apply WillSub.volitional_lift. Qed.
End TeloPraxis.