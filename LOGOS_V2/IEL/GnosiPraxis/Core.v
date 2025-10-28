From PXLs.Internal Emergent Logics.Pillars.GnosiPraxis.subdomains Require Import Truth.Spec.
Module GnosiPraxis.
  Definition V := PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.Truth.
  Theorem K_sound : forall p, V p -> Box V p.
  Proof. apply TruthSub.k_sound. Qed.
  Theorem Monotone : forall p q, (p -> q) -> Box V p -> Box V q.
  Proof. apply TruthSub.monotone. Qed.
  Theorem ClosureUnderMP : forall p q, Box (V p -> V q) -> Box V p -> Box V q.
  Proof. apply TruthSub.closure_under_mp. Qed.
End GnosiPraxis.

(* Exported capabilities *)
Class Cap_KnowledgeMonotone : Prop := { knowledge_monotone : forall p q, (p -> q) -> Box GnosiPraxis.V p -> Box GnosiPraxis.V q }.
Global Instance Cap_KnowledgeMonotone_inst : Cap_KnowledgeMonotone := {| knowledge_monotone := GnosiPraxis.Monotone |}.
Export Cap_KnowledgeMonotone.
