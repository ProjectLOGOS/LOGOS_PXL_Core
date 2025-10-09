From PXLs.IEL.Pillars.GnosiPraxis.subdomains Require Import Truth.Spec.
Module GnosiPraxis.
  Definition V := PXLs.IEL.Source.TheoPraxis.Props.Truth.
  Theorem K_sound : forall p, V p -> Box V p.
  Proof. apply TruthSub.k_sound. Qed.
  Theorem Monotone : forall p q, (p -> q) -> Box V p -> Box V q.
  Proof. apply TruthSub.monotone. Qed.
  Theorem ClosureUnderMP : forall p q, Box (V p -> V q) -> Box V p -> Box V q.
  Proof. apply TruthSub.closure_under_mp. Qed.
End GnosiPraxis.