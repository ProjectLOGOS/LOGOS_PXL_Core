From PXLs.IEL.Pillars.ThemiPraxis.subdomains Require Import Truth.Spec.
Module ThemiPraxis.
  Definition V := PXLs.IEL.Source.TheoPraxis.Props.Truth.
  Theorem DeonticDetachmentSafe : forall p, Box V p -> V p.
  Proof. apply TruthSub.deontic_detachment_safe. Qed.
End ThemiPraxis.