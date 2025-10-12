From PXLs Require Import PXLv3.
Require Import PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.
Module TruthSub.
  Import TheoProps.

  Context `{Cap_K_sound Truth} `{Cap_Monotone Truth} `{Cap_ClosureUnderMP Truth} `{Cap_ReflectsPXL Truth}.

  Definition V := Truth.

  Theorem conservative : forall p, V p -> p.
  Proof. apply cap_reflect. Qed.

  Theorem k_sound : forall p, Truth p -> Box Truth p.
  Proof. apply cap_ks. Qed.

  Theorem monotone : forall p q, (p -> q) -> Box Truth p -> Box Truth q.
  Proof. apply cap_mon. Qed.

  Theorem closure_under_mp : forall p q, Box (Truth p -> Truth q) -> Box Truth p -> Box Truth q.
  Proof. apply cap_mp. Qed.
End TruthSub.
