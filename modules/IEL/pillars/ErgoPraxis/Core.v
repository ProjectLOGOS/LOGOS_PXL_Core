From PXLs Require Import PXLv3.
From PXLs.IEL.Pillars.ErgoPraxis.subdomains Require Import Truth.Spec.
Module ErgoPraxis.
  Definition Valid := PXLs.IEL.Source.TheoPraxis.Props.Truth.
  Theorem SeqComp : forall p q r, Valid (p -> q) -> Valid (q -> r) -> Valid (p -> r).
  Proof. apply TruthSub.seq_comp. Qed.
  Theorem HoareTriples : forall p q, Valid p -> Valid (p -> q) -> Valid q.
  Proof. apply TruthSub.hoare_triples. Qed.
End ErgoPraxis.