From PXLs Require Import PXLv3.
Require Import PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.
Module TruthSub.
  Import TheoProps.

  Context `{Cap_SeqComp Truth} `{Cap_HoareTriples Truth} `{Cap_ReflectsPXL Truth}.

  Definition V := Truth.

  Theorem conservative : forall p, V p -> p.
  Proof. apply cap_reflect. Qed.

  Theorem seq_comp : forall p q r, Truth (p -> q) -> Truth (q -> r) -> Truth (p -> r).
  Proof. apply cap_sc. Qed.

  Theorem hoare_triples : forall p q, Truth p -> Truth (p -> q) -> Truth q.
  Proof. apply cap_ht. Qed.
End TruthSub.
