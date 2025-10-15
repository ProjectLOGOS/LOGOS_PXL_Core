From PXLs.Internal Emergent Logics.Pillars.ThemiPraxis.subdomains Require Import Truth.Spec.
Module ThemiPraxis.
  Definition V := PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.Truth.
  Theorem DeonticDetachmentSafe : forall p, Box V p -> V p.
  Proof. apply TruthSub.deontic_detachment_safe. Qed.
End ThemiPraxis.

(* Exported capabilities *)
Class Cap_SafeDetachment : Prop := { safe_detachment : forall p, Box ThemiPraxis.V p -> ThemiPraxis.V p }.
Global Instance Cap_SafeDetachment_inst : Cap_SafeDetachment := {| safe_detachment := ThemiPraxis.DeonticDetachmentSafe |}.
Export Cap_SafeDetachment.
