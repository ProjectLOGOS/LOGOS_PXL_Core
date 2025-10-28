From PXLs.IEL.Pillars.TeloPraxis.subdomains Require Import Will.Spec.
Module TeloPraxis.
  Definition V := PXLs.IEL.Source.TheoPraxis.Props.Will.
  Theorem EndMonotone : forall p q, (p -> q) -> V p -> V q.
  Proof. apply WillSub.end_monotone. Qed.
  Theorem VolitionalLift : forall p, V p -> Box V p.
  Proof. apply WillSub.volitional_lift. Qed.
End TeloPraxis.

(* Exported capabilities *)
Class Cap_EndMonotone : Prop := { end_monotone : forall p q, (p -> q) -> TeloPraxis.V p -> TeloPraxis.V q }.
Global Instance Cap_EndMonotone_inst : Cap_EndMonotone := {| end_monotone := TeloPraxis.EndMonotone |}.
Export Cap_EndMonotone.
