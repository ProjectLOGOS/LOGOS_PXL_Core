From PXLs Require Import PXLv3.
From PXLs.IEL.Pillars.ErgoPraxis.subdomains Require Import Truth.Spec.
Module ErgoPraxis.
  Definition Valid := PXLs.IEL.Source.TheoPraxis.Props.Truth.
  Theorem SeqComp : forall p q r, Valid (p -> q) -> Valid (q -> r) -> Valid (p -> r).
  Proof. apply TruthSub.seq_comp. Qed.
  Theorem HoareTriples : forall p q, Valid p -> Valid (p -> q) -> Valid q.
  Proof. apply TruthSub.hoare_triples. Qed.
End ErgoPraxis.

(* Exported capabilities *)
Class Cap_HoareStable : Prop := { hoare_stable : forall p q, ErgoPraxis.Valid p -> ErgoPraxis.Valid (p -> q) -> ErgoPraxis.Valid q }.
Global Instance Cap_HoareStable_inst : Cap_HoareStable := {| hoare_stable := ErgoPraxis.HoareTriples |}.
Export Cap_HoareStable.
