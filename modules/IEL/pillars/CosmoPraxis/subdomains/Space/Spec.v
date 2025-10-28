From PXLs Require Import PXLv3.
Require Import PXLs.IEL.Source.TheoPraxis.Props.
Module SpaceSub.
  Import TheoProps.

  Context `{Cap_ChronoTopoInterface Space} `{Cap_ReflectsPXL Space}.

  Definition V := Space.

  Theorem conservative : forall p, V p -> p.
  Proof. apply cap_reflect. Qed.

  Theorem chrono_topo_interface : forall p, Space p -> Space (Box p).
  Proof. apply cap_cti. Qed.
End SpaceSub.
