From PXLs Require Import PXLv3.
Require Import PXLs.IEL.Source.TheoPraxis.Props.
Module LifeSub.
  Import TheoProps.

  Context `{Cap_AgentCapability Life} `{Cap_AgencyComp Life} `{Cap_ReflectsPXL Life}.

  Definition V := Life.

  Theorem conservative : forall p, V p -> p.
  Proof. apply cap_reflect. Qed.

  Theorem agent_capability : forall p, Life p -> Dia Life p.
  Proof. apply cap_ac. Qed.

  Theorem agency_comp : forall p q, Life p -> Life q -> Life (p /\ q).
  Proof. apply cap_ag. Qed.
End LifeSub.
