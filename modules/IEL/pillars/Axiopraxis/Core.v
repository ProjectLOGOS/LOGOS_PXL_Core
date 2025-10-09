From PXLs.Core Require Import PXL_Kernel.
From PXLs.IEL.Pillars.Axiopraxis.subdomains Require Import Truth.Spec Beauty.Spec.
Module Axiopraxis.
  Definition V := TheoProps.Truth.  (* canonical carrier *)

  Theorem ValueMonotone : forall p q, (p -> q) -> V p -> V q.
  Proof. apply TruthSub.monotone. Qed.

  Theorem ConjElim : forall p q, V (p /\ q) -> V p /\ V q.
  Proof.
    (* derive via Beauty's capability and a lemma relating Beauty to V if needed *)
  Admitted. (* replace by bridging lemma Beauty->Truth or choose Beauty as V *)

  Theorem NonExplosion : ~ V False.
  Proof. apply TruthSub.non_explosion. Qed.

  Theorem Conservativity : forall p, V p -> p.
  Proof. apply TruthSub.conservative. Qed.
End Axiopraxis.