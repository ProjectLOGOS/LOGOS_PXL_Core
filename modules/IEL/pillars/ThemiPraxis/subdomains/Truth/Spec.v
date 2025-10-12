From PXLs Require Import PXLv3.
Require Import PXLs.Internal Emergent Logics.Source.TheoPraxis.Props.
Module TruthSub.
  Import TheoProps.

  Context `{Cap_DeonticDetachmentSafe Truth} `{Cap_ReflectsPXL Truth}.

  Definition V := Truth.

  Theorem conservative : forall p, V p -> p.
  Proof. apply cap_reflect. Qed.

  Theorem deontic_detachment_safe : forall p, Box Truth p -> Truth p.
  Proof. apply cap_dds. Qed.
End TruthSub.
