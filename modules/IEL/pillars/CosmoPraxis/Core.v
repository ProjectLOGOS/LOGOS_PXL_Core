From PXLs.IEL.Pillars.CosmoPraxis.subdomains Require Import Space.Spec.
Module CosmoPraxis.
  Definition V := PXLs.IEL.Source.TheoPraxis.Props.Space.
  Theorem ChronoTopoInterface : forall p, V p -> V (Box p).
  Proof. apply SpaceSub.chrono_topo_interface. Qed.
End CosmoPraxis.