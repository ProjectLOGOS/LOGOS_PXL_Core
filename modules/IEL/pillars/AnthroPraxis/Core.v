From PXLs.IEL.Pillars.AnthroPraxis.subdomains Require Import Life.Spec.
Module AnthroPraxis.
  Definition V := PXLs.IEL.Source.TheoPraxis.Props.Life.
  Theorem AgentCapability : forall p, V p -> Dia V p.
  Proof. apply LifeSub.agent_capability. Qed.
  Theorem AgencyComp : forall p q, V p -> V q -> V (p /\ q).
  Proof. apply LifeSub.agency_comp. Qed.
End AnthroPraxis.