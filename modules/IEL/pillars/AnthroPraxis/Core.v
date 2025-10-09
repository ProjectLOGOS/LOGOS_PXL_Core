From PXLs.IEL.Pillars.AnthroPraxis.subdomains Require Import Life.Spec.
Module AnthroPraxis.
  Definition V := PXLs.IEL.Source.TheoPraxis.Props.Life.
  Theorem AgentCapability : forall p, V p -> Dia V p.
  Proof. apply LifeSub.agent_capability. Qed.
  Theorem AgencyComp : forall p q, V p -> V q -> V (p /\ q).
  Proof. apply LifeSub.agency_comp. Qed.
End AnthroPraxis.

(* Exported capabilities *)
Class Cap_AgencyCompat : Prop := { agency_compat : forall p q, AnthroPraxis.V p -> AnthroPraxis.V q -> AnthroPraxis.V (p /\ q) }.
Global Instance Cap_AgencyCompat_inst : Cap_AgencyCompat := {| agency_compat := AnthroPraxis.AgencyComp |}.
Export Cap_AgencyCompat.
